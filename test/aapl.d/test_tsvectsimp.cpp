/*
 * Copyright 2003 Adrian Thurston <thurston@colm.net>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include <iostream>
#include "tsvectsimp.h"
#include "svectsimp.h"
#include "svector.h"

using namespace std;

struct POD1 { POD1(int i, int j) : i(i),j(j) {} int i, j; };
struct POD2 { POD2(int i, int j) : i(i),j(j) {} int i, j; };
struct POD3 { POD3(int i, int j) : i(i),j(j) {} int i, j; };
struct POD4 { POD4(int i, int j) : i(i),j(j) {} int i, j; };
struct POD5 { POD5(int i, int j) : i(i),j(j) {} int i, j; };
struct POD6 { POD6(int i, int j) : i(i),j(j) {} int i, j; };

#define TINY_VECT

#ifdef TINY_VECT
typedef TSVectSimp<POD1> Vect1;
typedef TSVectSimp<POD2> Vect2;
typedef TSVectSimp<POD3> Vect3;
typedef TSVectSimp<POD4> Vect4;
typedef TSVectSimp<POD5> Vect5;
typedef TSVectSimp<POD6> Vect6;
#else
typedef SVectSimp<POD1> Vect1;
typedef SVectSimp<POD2> Vect2;
typedef SVectSimp<POD3> Vect3;
typedef SVectSimp<POD4> Vect4;
typedef SVectSimp<POD5> Vect5;
typedef SVectSimp<POD6> Vect6;
#endif

//template TSVectSimp<POD1>;
//template TSVectSimp<POD2>;
//template TSVectSimp<POD3>;
//template TSVectSimp<POD4>;
//template TSVectSimp<POD5>;
//template TSVectSimp<POD6>;

void testTSVectSimp1()
{
	POD1 pod(1,2);
	Vect1 b;
	for (int i = 0; i < 1000000; i++ )
		b.append(pod);
	for ( Vect1::Iter i = b.first(); i.lte(); i++ )
		i->i = i->j + 1;
}

void testTSVectSimp2()
{
	POD2 pod(3,4);
	Vect2 b;
	for (int i = 0; i < 1000000; i++ )
		b.append(pod);
	for ( Vect2::Iter i = b.first(); i.lte(); i++ )
		i->i = i->j + 1;
}

void testTSVectSimp3()
{
	POD3 pod(5,6);
	Vect3 b;
	for (int i = 0; i < 1000000; i++ )
		b.append(pod);
	for ( Vect3::Iter i = b.first(); i.lte(); i++ )
		i->i = i->j + 1;
}

void testTSVectSimp4()
{
	POD4 pod(7,8);
	Vect4 b;
	for (int i = 0; i < 1000000; i++ )
		b.append(pod);
	for ( Vect4::Iter i = b.first(); i.lte(); i++ )
		i->i = i->j + 1;
}

void testTSVectSimp5()
{
	POD5 pod(9,10);
	Vect5 b;
	for (int i = 0; i < 1000000; i++ )
		b.append(pod);
	for ( Vect5::Iter i = b.first(); i.lte(); i++ )
		i->i = i->j + 1;
}

void testTSVectSimp6()
{
	POD6 pod(11,12);
	Vect6 b;
	for (int i = 0; i < 1000000; i++ )
		b.append(pod);
	for ( Vect6::Iter i = b.first(); i.lte(); i++ )
		i->i = i->j + 1;
}

int main()
{
	testTSVectSimp1();
	testTSVectSimp2();
	testTSVectSimp3();
	testTSVectSimp4();
	testTSVectSimp5();
	testTSVectSimp6();
	return 0;
}
