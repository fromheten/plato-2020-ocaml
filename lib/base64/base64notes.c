/* Base64 encode IN array of size INLEN into OUT array of size OUTLEN.
63 	   If OUTLEN is less than BASE64_LENGTH(INLEN), write as many bytes as
64 	   possible.  If OUTLEN is larger than BASE64_LENGTH(INLEN), also zero
65 	   terminate the output buffer. */
66 	void
67 	base64_encode (const char *restrict in, size_t inlen,
68 	               char *restrict out, size_t outlen)
69 	{
70 	  static const char b64str[64] =
71 	    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
72
73 	  while (inlen && outlen)
74 	    {
  /* Take the first byte, bitshift 2 steps, and set the first 2 bits to 0
This because we want to take 6 bits, as there are 64 possible combinations of 6 bits
example:
in[0] = 10101011
>> 2
-> 11101010
&  00111111 # = 0x3f
-> 00101010 # = 42
 */
75 	      *out++ = b64str[(to_uchar (in[0]) >> 2) & 0x3f];
76 	      if (!--outlen)
77 	        break;
/* Now we want 6 bits, but skipping the first 6 bits that we already used
Example:

in[0] = 10101010
<< 4
-> 10100000

in[1] = 11001100
>> 4
-> 00001100

Now we have the 2nd half of the first byte, and the 1st half of the second byte
10100000 + 00001100
-> 10101100
Great! Now remove the 2 leftmost bits
& 0x3f # 00111111
-> 00101100

Now we have bits from position 6-12 :-) yay
*/
78 	      *out++ = b64str[((to_uchar (in[0]) << 4)
79 	                       + (--inlen ? to_uchar (in[1]) >> 4 : 0))
80 	                      & 0x3f];
81 	      if (!--outlen)
82 	        break;
83 	      *out++ =
84 	        (inlen
                 /*
in[1] = 11001100
<< 2
-> 00110000
in[2] = 11011011
>> 6 # essentially cut the 2 leftmost bits
-> 00000011

Then sum them
00110000 + 00000011
-> 00110011
& 00111111
-> 00110011 # = 51 in decimal
 */
85 	         ? b64str[((to_uchar (in[1]) << 2)
86 	                   + (--inlen ? to_uchar (in[2]) >> 6 : 0))
87 	                  & 0x3f]
88 	         : '=');
89 	      if (!--outlen)
90 	        break;
/* Here we are only interested in the last 6 bits of in[2], as we already consumed the first 2 bits of it
in[2] = 11011011
& 00111111
-> 00011011 */
91 	      *out++ = inlen ? b64str[to_uchar (in[2]) & 0x3f] : '=';
92 	      if (!--outlen)
93 	        break;
94 	      if (inlen)
95 	        inlen--;
96 	      if (inlen)
/* Drop the first 3 characters - we have consumed them */
97 	        in += 3;
98 	    }
99
100 	  if (outlen)
101 	    *out = '\0';
102 	}


303 	/* Decode base64 encoded input array IN of length INLEN to output
304 	   array OUT that can hold *OUTLEN bytes.  Return true if decoding was
305 	   successful, i.e. if the input was valid base64 data, false
306 	   otherwise.  If *OUTLEN is too small, as many bytes as possible will
307 	   be written to OUT.  On return, *OUTLEN holds the length of decoded
308 	   bytes in OUT.  Note that as soon as any non-alphabet characters are
309 	   encountered, decoding is stopped and false is returned.  This means
310 	   that, when applicable, you must remove any line terminators that is
311 	   part of the data stream before calling this function.  */
312 	bool
313 	base64_decode (const char *restrict in, size_t inlen,
314 	               char *restrict out, size_t *outlen)
315 	{
  /* Size of output buffer - how much am I allowed to write */
316 	  size_t outleft = *outlen;
317
318 	  while (inlen >= 2)
319 	    {
320 	      if (!isbase64 (in[0]) || !isbase64 (in[1]))
321 	        break;
322
323 	      if (outleft)
  /*
Keep in mind, a valid Base64 char always begins with 00
in[0] = 00101010
<< 2
-> 10101000
in[1] = 00100111
>> 4
-> 00000010
   10101000
|  00000010
-> 10101010
We now have 8 bits - 6 from the first byte, and 2 from the 2nd byte
 */
324 	        {
325 	          *out++ = ((b64[to_uchar (in[0])] << 2)
326 	                    | (b64[to_uchar (in[1])] >> 4));
327 	          outleft--;
328 	        }
329
330 	      if (inlen == 2)
331 	        break;
332
/* It does not make sense if there are more than 2 padding signs here */
333 	      if (in[2] == '=')
334 	        {
335 	          if (inlen != 4)
336 	            break;
337
338 	          if (in[3] != '=')
339 	            break;
340
341 	        }
342 	      else
343 	        {
344 	          if (!isbase64 (in[2]))
345 	            break;
346
347 	          if (outleft)
  /*
in[1] = 00100111
<< 4
-> 01110000
& 0xf0
-> 01110000

in[2] = 00111101
>> 2
-> 00001111

   01110000
|  00001111
-> 01111111

 */
348 	            {
349 	              *out++ = (((b64[to_uchar (in[1])] << 4) & 0xf0)
350 	                        | (b64[to_uchar (in[2])] >> 2));
351 	              outleft--;
352 	            }
353
354 	          if (inlen == 3)
355 	            break;
356
/* If there is only one padding here, we are done */
357 	          if (in[3] == '=')
358 	            {
359 	              if (inlen != 4)
360 	                break;
361 	            }
362 	          else
363 	            {
364 	              if (!isbase64 (in[3]))
365 	                break;
366
367 	              if (outleft)
  /*
in[2] = 00111101
<< 6
-> 01000000
& 0xc0 # = 11000000 just assert we take the first 2 bits
-> 01000000
in[3] = 00011010

   01000000
|  00011010
-> 01011010
 */
368 	                {
369 	                  *out++ = (((b64[to_uchar (in[2])] << 6) & 0xc0)
370 	                            | b64[to_uchar (in[3])]);
371 	                  outleft--;
372 	                }
373 	            }
374 	        }
375
376 	      in += 4;
377 	      inlen -= 4;
378 	    }
379
380 	  *outlen -= outleft;
381
382 	  if (inlen != 0)
383 	    return false;
384
385 	  return true;
386 	}
