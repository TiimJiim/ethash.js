// ethash.js
// Tim Hughes <tim@twistedfury.com>

/*jslint node: true, shadow:true */
"use strict";

var Keccak = require('./keccak');
var util = require('./util');

// 32-bit unsigned modulo
function mod32(x, n)
{
	return (x>>>0) % (n>>>0);
}

// 64-bit unsigned modulo
function mod64(lo, hi, n)
{
	lo >>>= 0;
	hi >>>= 0;
	n >>>= 0;
	return ((0x100000000*hi % n) + lo) % n;
}

// fast 32-bit multiply modulo: (a * b) % m
function modMul32(a, b, m)
{
	var lo = a & 0xffff;
	var hi = a - lo;
	return (lo*b + (hi*b % m)) % m;
}

function modPow32(b, e, m)
{
	b >>>= 0;
	e >>>= 0;
	m >>>= 0;
	
	var r = 1;
	for (var i = 31; i >= 0; i = (i-1)|0)
	{
		if (r > 1)
			r = modMul32(r, r, m);
			
		if ((e>>i) & 1)
			r = modMul32(r, b, m);
	}
    return r;
}

var P1 = 4294967087;
var P2 = 4294963787;

function bbsStep(n, P)
{
	return modMul32(modMul32(n, n, P), n, P);
}

function bbsAdvance(n, i, P)
{
	return modPow32(n, modPow32(3, i, (P-1)>>>0), P);
}

function bbsClamp(n, P)
{
	// ensure int32->uint32
	n >>>= 0;
	P >>>= 0;
	
    if (n < 2)
		return 2;
    if (n > P - 2)
		return P - 2;
    return n;
}

function fnv(x, y)
{
	// js integer multiply by 0x01000193 will lose precision
	return ((x*0x01000000 | 0) + (x*0x193 | 0)) ^ y;	
}

function computeCache(params, seedWords)
{
	var cache = new Uint32Array(params.cacheSize >> 2);
	var cacheNodeCount = params.cacheSize >> 6;

	// Initialize cache
	var keccak = new Keccak();
	keccak.digestWords(cache, 0, 16, seedWords, 0, seedWords.length);
	for (var n = 1; n < cacheNodeCount; ++n)
	{
		keccak.digestWords(cache, n<<4, 16, cache, (n-1)<<4, 16);
	}
	
	var join = new Uint32Array(32);
	
	// Do randmemohash passes
	for (var r = 0; r < params.cacheRounds; ++r)
	{
		for (var n = 0; n < cacheNodeCount; ++n)
		{
			var p0 = mod32(n + cacheNodeCount - 1, cacheNodeCount) << 4;
			var p1 = mod64(cache[n<<4|0], cache[n<<4|1], cacheNodeCount) << 4;
			
			for (var w = 0; w < 16; w=(w+1)|0)
			{
				// todo, reconcile with spec
				// spec says concatonate, would prefer XOR for speed
				//join[w] = cache[p0 | w] ^ cache[p1 | w];
				join[w] = cache[p0 | w];
				join[w|16] = cache[p1 | w];
			}
			
			keccak.digestWords(cache, n<<4, 16, join, 0, join.length);
		}
	}	
	return cache;
}

function computeDagNode(o_node, params, cache, rand1, nodeIndex)
{
	var cacheNodeCount = params.cacheSize >> 6;
	var dagParents = params.dagParents >> 0;
	
	// initialise second random number generator
    var rand2 = bbsClamp(bbsAdvance(rand1, nodeIndex, P1), P2);
	
	// initialise mix with some data from the cache
	var c = (nodeIndex % cacheNodeCount) << 4;
	var mix = o_node;
	for (var w = 0; w < 16; ++w)
	{
		mix[w] = cache[c|w];
	}
	
	for (var p = 0; p < dagParents; p = (p+1)|0)
	{
		// compute cache node (word) index
		c = mod32(mix[p&15] ^ rand2, cacheNodeCount) << 4;
		
		for (var w = 0; w < 16; ++w)
		{
			mix[w] = fnv(mix[w], cache[c|w]);
		}
		
		rand2 = bbsStep(rand2, P2);
	}
}

function computeHashInner(mix, params, cache, rand1, tempNode)
{
	var mixParents = params.mixParents| 0;
	var mixWordCount = params.mixSize >> 2;
	var mixNodeCount = mixWordCount >> 4;
	var dagPageCount = (params.dagSize / params.mixSize) >> 0;
	
	// initialise mix from initial 64 bytes
	for (var w = 16; w < (mixWordCount+16)|0; w = (w+1)|0)
	{
		mix[w] = mix[w & 15];
	}
	
	var rand2 = bbsClamp(mix[0], P2);
	for (var a = 0; a < mixParents; a = (a+1)|0)
	{
		var d = (mod32(mix[a & (mixWordCount - 1)] ^ rand2, dagPageCount) * mixNodeCount)|0;
		
		for (var n = 0, w = 16; n < mixNodeCount; n = (n+1)|0)
		{
			computeDagNode(tempNode, params, cache, rand1, (d + n)|0);
			
			for (var v = 0; v < 16; v = (v+1)|0, w = (w+1)|0)
			{
				mix[w] = fnv(mix[w], tempNode[v]);
			}
		}
		
        rand2 = bbsStep(rand2, P2);
	}
}

function convertSeed(seed)
{
	// todo, reconcile with spec, byte ordering?
	// todo, big-endian conversion
	var newSeed = util.toWords(seed);
	if (newSeed === null)
		throw Error("Invalid seed '" + seed + "'");
	return newSeed;
}

exports.defaultParams = function()
{
	return {
		cacheSize: 8209 * 4096,	// multiple of mixSize
		cacheRounds: 2,
		dagSize: 262147 * 4096,	// multiple of mixSize
		dagParents: 64,
		mixSize: 4096,
		mixParents: 32,
	};
};

exports.Ethash = function(params, seed)
{
	// precompute cache and related values
	seed = convertSeed(seed);
	var cache = computeCache(params, seed);
	var rand1 = bbsClamp(cache[0], P1);
	
	// preallocate buffers/etc
	var mixBuf = new ArrayBuffer(64 + params.mixSize);
	var mixBytes = new Uint8Array(mixBuf);
	var mixWords = new Uint32Array(mixBuf);
	var tempNode = new Uint32Array(16);
	var keccak = new Keccak();
	
	var retWords = new Uint32Array(8);
	var retBytes = new Uint8Array(retWords.buffer); // supposedly read-only
	
	this.hash = function(header, nonce)
	{
		// compute initial hash
		// todo: reconcile with spec, byte ordering?
		// todo: big-endian conversion. Ideally header/nonce are in little endian format.
		mixBytes.set(header, 0);
		mixBytes.set(nonce, 32);
		keccak.digestWords(mixWords, 0, 16, mixWords, 0, 16);
		
		// compute mix
		computeHashInner(mixWords, params, cache, rand1, tempNode);
		
		// final Keccak hashes
		keccak.digestWords(mixWords, 16, 8, mixWords, 0, mixWords.length);	// Keccak-256(s + mix)
		keccak.digestWords(retWords, 0, 8, mixWords, 0, 24);				// Keccak-256(s + Keccak-256(s + mix))
		return retBytes;
	};
	
	this.cacheDigest = function()
	{
		return keccak.digest(32, new Uint8Array(cache.buffer));
	};
};




