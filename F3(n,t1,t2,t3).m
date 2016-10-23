//------------------------------------------------------------------------------------------------------------------------------//
// Filename: F3(n,t1,t2,t3).m
//
// Purpose:  This magma code computes Z_1(i*f) for i in [0..26] and f = (T_3,T_2,T_1) for n = 1,2,4,5,7,8 (mod 9), and then applies Transform 2 to give 
// N(j) for j in [0..26].
//
// Date: 21st October 2016
// Author: Robert Granger		
//------------------------------------------------------------------------------------------------------------------------------//

//The following store the vector of Z_1(i*f) for i in [3..26] and n = 1,2,4,5,7,8 (mod 9). Note that we ignore Z_1(0*f) = 3^n 
//and Z_1(1*f) = Z_1(2*f) = 3^(n-1) and the first three columns of the matrix, and focus on the roots of the L-polynomials only. 
Z1 := [];
Z2 := [];
Z4 := [];
Z5 := [];
Z7 := [];
Z8 := [];

//--------------------------------------------------------------------------------------------------------------------------------

//Compute the relevant L-polynomials when the first 2 and 3 coefficients are prescribed, i.e., Z_1(i*f) for i in [3..26] and
//f = (T_3,T_2,T_1), and n = 1,2,4,5,7,8 (mod 9).

//Notes:

//We combine 2 and 3 because they both use two auxiliary variables to define the relevant curves.
//outL3 takes input i in [3..26] and n either 1,2,4,5,7,8 representing these residue classes mod 9 and returns the L-polynomial. 

//--------------------------------------------------------------------------------------------------------------------------------
//Setup

//This is for the L-polynomials
P<X> := PolynomialRing(Integers());

//This is ambient space of the curves
F3 := GF(3);
A2<a0,a1> := AffineSpace(F3,2);

//Ternary expansion of input integer i, assumed to be 3 trits long.
base3 := function( i );
  out := [];
  tmp := i;
  for j in [1..3] do
    out[4-j] := tmp mod 3;
    tmp := (tmp - out[4-j]) div 3;
  end for;
  return out;
end function;

//----------------------------------------------------------------------------------------------------------------------------------

//Need to define the trace forms, dependent on B := [B[1],B[2],B[3]] vector, so define as a function. 
//Tr[i] is T_(4-i)(x^3 - x + r0), i.e., the base elements for the linear combinations.
forms := function( B, r0, n );
  Tr := [];
  Tr[1] := a0^7 - a0^5 + r0*(B[1] + 1)*(a0^4 - a0^2) + r0*B[3]*InverseMod(n,3);
  Tr[2] := a0^4 - a0^2 - r0*B[2]*InverseMod(n,3);
  Tr[3] := r0;
  return Tr;
end function;


//This is the main function for 3 coefficients. i should be in [3..26] and n either 1,2,4,5,7,8 representing those n equal to this mod 9
//Values for T1(1),T2(1),T3(1) depend on n mod 9. These are B := [B[1],B[2],B[3]].
outL3 := function( i, n );

  i3 := base3(i);

  if n eq 1 then 
    B := [1,0,0];
  elif n eq 2 then
    B := [2,1,0];
  elif n eq 4 then
    B := [1,0,1];
  elif n eq 5 then
    B := [2,1,1];
  elif n eq 7 then
    B := [1,0,2];
  elif n eq 8 then
    B := [2,1,2];   
  end if;

  L := 1;

  for r0 in F3 do
    Tr := forms( B, r0, n );
    c1 := (a1^3 - a1 + InverseMod(n,3)) - &+[i3[j]*Tr[j]: j in [1..3]];
    I := ideal< CoordinateRing(A2) | c1>; 
    C := Curve(A2,I);
    L := L*P!LPolynomial(C);
  end for;
 
  return ReciprocalPolynomial(L);
end function;

//Output needed
for i in [3..26] do
  Z1[i-2] := outL3(i,1);
  Z2[i-2] := outL3(i,2);
  Z4[i-2] := outL3(i,4);
  Z5[i-2] := outL3(i,5);
  Z7[i-2] := outL3(i,7);
  Z8[i-2] := outL3(i,8);
end for;

//-------------------------------------------------------------------------------------------------------

//This is 9 * S_3^(-1) with the first three columns deleted.
M := Matrix(27,24,[
[-1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1],
[-1 , 1 , 0 , -1 , 1 , 0 , -1 , 1 , 0 , -1 , 1 , 0 , -1 , 1 , 0 , -1 , 1 , 0 , -1 , 1 , 0 , -1 , 1 , 0],
[-1 , 0 , 1 , -1 , 0 , 1 , -1 , 0 , 1 , -1 , 0 , 1 , -1 , 0 , 1 , -1 , 0 , 1 , -1 , 0 , 1 , -1 , 0 , 1],
[1 , 1 , 1 , 0 , 0 , 0 , -1 , -1 , -1 , 1 , 1 , 1 , 0 , 0 , 0 , -1 , -1 , -1 , 1 , 1 , 1 , 0 , 0 , 0],
[1 , 0 , -1 , 0 , -1 , 1 , -1 , 1 , 0 , 1 , 0 , -1 , 0 , -1 , 1 , -1 , 1 , 0 , 1 , 0 , -1 , 0 , -1 , 1],
[1 , -1 , 0 , 0 , 1 , -1 , -1 , 0 , 1 , 1 , -1 , 0 , 0 , 1 , -1 , -1 , 0 , 1 , 1 , -1 , 0 , 0 , 1 , -1],
[0 , 0 , 0 , 1 , 1 , 1 , -1 , -1 , -1 , 0 , 0 , 0 , 1 , 1 , 1 , -1 , -1 , -1 , 0 , 0 , 0 , 1 , 1 , 1],
[0 , -1 , 1 , 1 , 0 , -1 , -1 , 1 , 0 , 0 , -1 , 1 , 1 , 0 , -1 , -1 , 1 , 0 , 0 , -1 , 1 , 1 , 0 , -1],
[0 , 1 , -1 , 1 , -1 , 0 , -1 , 0 , 1 , 0 , 1 , -1 , 1 , -1 , 0 , -1 , 0 , 1 , 0 , 1 , -1 , 1 , -1 , 0],
[-1 , -1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0],
[-1 , 1 , 0 , -1 , 1 , 0 , 1 , 0 , -1 , 1 , 0 , -1 , 1 , 0 , -1 , 0 , -1 , 1 , 0 , -1 , 1 , 0 , -1 , 1], 
[-1 , 0 , 1 , -1 , 0 , 1 , 1 , -1 , 0 , 1 , -1 , 0 , 1 , -1 , 0 , 0 , 1 , -1 , 0 , 1 , -1 , 0 , 1 , -1],
[1 , 1 , 1 , 0 , 0 , 0 , 1 , 1 , 1 , 0 , 0 , 0 , -1 , -1 , -1 , 0 , 0 , 0 , -1 , -1 , -1 , 1 , 1 , 1], 
[1 , 0 , -1 , 0 , -1 , 1 , 1 , 0 , -1 , 0 , -1 , 1 , -1 , 1 , 0 , 0 , -1 , 1 , -1 , 1 , 0 , 1 , 0 , -1], 
[1 , -1 , 0 , 0 , 1 , -1 , 1 , -1 , 0 , 0 , 1 , -1 , -1 , 0 , 1 , 0 , 1 , -1 , -1 , 0 , 1 , 1 , -1 , 0], 
[0 , 0 , 0 , 1 , 1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , 0 , 0 , 0 , 0 , 0 , 0 , 1 , 1 , 1 , -1 , -1 , -1],
[0 , -1 , 1 , 1 , 0 , -1 , 1 , 0 , -1 , -1 , 1 , 0 , 0 , -1 , 1 , 0 , -1 , 1 , 1 , 0 , -1 , -1 , 1 , 0],
[0 , 1 , -1 , 1 , -1 , 0 , 1 , -1 , 0 , -1 , 0 , 1 , 0 , 1 , -1 , 0 , 1 , -1 , 1 , -1 , 0 , -1 , 0 , 1],
[-1 , -1 , -1 , -1 , -1 , -1 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 0 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1],
[-1 , 1 , 0 , -1 , 1 , 0 , 0 , -1 , 1 , 0 , -1 , 1 , 0 , -1 , 1 , 1 , 0 , -1 , 1 , 0 , -1 , 1 , 0 , -1],
[-1 , 0 , 1 , -1 , 0 , 1 , 0 , 1 , -1 , 0 , 1 , -1 , 0 , 1 , -1 , 1 , -1 , 0 , 1 , -1 , 0 , 1 , -1 , 0], 
[1 , 1 , 1 , 0 , 0 , 0 , 0 , 0 , 0 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , 1 , 1 , 0 , 0 , 0 , -1 , -1 , -1],
[1 , 0 , -1 , 0 , -1 , 1 , 0 , -1 , 1 , -1 , 1 , 0 , 1 , 0 , -1 , 1 , 0 , -1 , 0 , -1 , 1 , -1 , 1 , 0],
[1 , -1 , 0 , 0 , 1 , -1 , 0 , 1 , -1 , -1 , 0 , 1 , 1 , -1 , 0 , 1 , -1 , 0 , 0 , 1 , -1 , -1 , 0 , 1], 
[0 , 0 , 0 , 1 , 1 , 1 , 0 , 0 , 0 , 1 , 1 , 1 , -1 , -1 , -1 , 1 , 1 , 1 , -1 , -1 , -1 , 0 , 0 , 0], 
[0 , -1 , 1 , 1 , 0 , -1 , 0 , -1 , 1 , 1 , 0 , -1 , -1 , 1 , 0 , 1 , 0 , -1 , -1 , 1 , 0 , 0 , -1 , 1],
[0 , 1 , -1 , 1 , -1 , 0 , 0 , 1 , -1 , 1 , -1 , 0 , -1 , 0 , 1 , 1 , -1 , 0 , -1 , 0 , 1 , 0 , 1 , -1]
]);

//--------------------------------------------------------------------------------------------------------------------------------------

//This computes the L-polynomial expressions for Nn(j) and Zn with n = 1,2,4,5,7,8 
computequo := function( j, Z );

  num := 1;
  den := 1;

  for k in [1..24] do
    if M[j,k] eq 1 then
      num := num*Z[k];
    elif M[j,k] eq -1 then  
      den := den*Z[k];  
    end if;
  end for;

  return num/den;
end function;


//Computes the L-polynomial expressions for N1(j) for j in [0..26], for n = 1 (mod 9). Remember that Magma arrays start from 1, not 0.
N1 := [];

//Compute N1[1] last in order to avoid a sequence mutation
for j in [2..27] do
  N1[j] := computequo(j, Z1);
  print j;
  Factorisation(Numerator(N1[j]));
  Factorisation(Denominator(N1[j]));
end for;

N1[1] := computequo(1, Z1);

//Computes the L-polynomial expressions for N2(j) for j in [0..26], for n = 2 (mod 9).
N2 := [];

//Compute N2[1] last in order to avoid a sequence mutation
for j in [2..27] do
  N2[j] := computequo(j, Z2);
  print j;
  Factorisation(Numerator(N2[j]));
  Factorisation(Denominator(N2[j]));
end for;

N2[1] := computequo(1, Z2);

//Computes the L-polynomial expressions for N4(j) for j in [0..26], for n = 4 (mod 9). Remember that Magma arrays start from 1, not 0.
N4 := [];

//Compute N4[1] last in order to avoid a sequence mutation
for j in [2..27] do
  N4[j] := computequo(j, Z4);
  print j;
  Factorisation(Numerator(N4[j]));
  Factorisation(Denominator(N4[j]));
end for;

N4[1] := computequo(1, Z4);

//Computes the L-polynomial expressions for N5(j) for j in [0..26], for n = 5 (mod 9). Remember that Magma arrays start from 1, not 0.
N5 := [];

//Compute N5[1] last in order to avoid a sequence mutation
for j in [2..27] do
  N5[j] := computequo(j, Z5);
  print j;
  Factorisation(Numerator(N5[j]));
  Factorisation(Denominator(N5[j]));
end for;

N5[1] := computequo(1, Z5);

//Computes the L-polynomial expressions for N7(j) for j in [0..26], for n = 7 (mod 9). Remember that Magma arrays start from 1, not 0.
N7 := [];

//Compute N7[1] last in order to avoid a sequence mutation
for j in [2..27] do
  N7[j] := computequo(j, Z7);
  print j;
  Factorisation(Numerator(N7[j]));
  Factorisation(Denominator(N7[j]));
end for;

N7[1] := computequo(1, Z7);

//Computes the L-polynomial expressions for N8(j) for j in [0..26], for n = 8 (mod 9). Remember that Magma arrays start from 1, not 0.
N8 := [];

//Compute N8[1] last in order to avoid a sequence mutation
for j in [2..27] do
  N8[j] := computequo(j, Z8);
  print j;
  Factorisation(Numerator(N8[j]));
  Factorisation(Denominator(N8[j]));
end for;

N8[1] := computequo(1, Z8);


//--------------------------------------------------------------------------------------------------------------------------------
//Since some of the occurring irreducible factors f(X) equal g(-X) for other occurring factors, we cancel the cancelling roots and 
//combine those that do not.

//Running through the F(n,0,0,0) polynomials the features ones are:
f := [];
f[1] := X^2 - 3*X + 3; //p2,1
f[2] := X^2 + 3*X + 3; //p2,2
f[3] := X^2 + 3; //p2,3
f[4] := X^6 + 3*X^5 + 9*X^4 + 15*X^3 + 27*X^2 + 27*X + 27; //p6
f[5] := X^12 - 3*X^11 + 3*X^9 + 9*X^8 - 45*X^6 + 81*X^4 + 81*X^3 - 729*X + 729; //p12,1
f[6] := X^12 - 3*X^11 + 12*X^9 - 18*X^8 - 27*X^7 + 117*X^6 - 81*X^5 - 162*X^4 + 324*X^3 - 729*X + 729; //p12,2
f[7] := X^12 - 3*X^11 + 9*X^10 - 15*X^9 + 36*X^8 - 54*X^7 + 117*X^6 - 162*X^5 + 324*X^4 - 405*X^3 + 729*X^2 - 729*X + 729; //p12,3
f[8] := X^12 + 6*X^11 + 18*X^10 + 39*X^9 + 63*X^8 + 81*X^7 + 117*X^6 + 243*X^5 + 567*X^4 + 1053*X^3 + 1458*X^2 + 1458*X + 729; //p12,4


//This function rewrites an input poly over the factors of f[], with exponents, allowing for cancellations, and denominators.
//Input is Nn[j] = num/den
rewritefactors := function( quo );

  num := Numerator(quo);
  den := Denominator(quo);

  Facnum := Factorisation(num);
  Facden := Factorisation(den);

  temp1 := [0,0,0,0,0,0,0,0];
  for i in [1..#Facnum] do
    temp1[Index(f,Facnum[i][1])] := Facnum[i][2];
  end for;

  temp2 := [0,0,0,0,0,0,0,0];
  for i in [1..#Facden] do
    temp2[Index(f,Facden[i][1])] := Facden[i][2];
  end for;

  temp := [];
  for i in [1..8] do
    temp[i] := temp1[i] - temp2[i];
  end for;

  return temp;

end function;


//-------------------------------------------------------------------------------------------

//Output function for ease of viewing. Input is Nn[j].
//Note that we must divide the exponents by 3^2, since there are 2 variables. We must also divide by 9, since this is the denominator of the matrix.

//This is the output function
out := function( j );
  temp1 := rewritefactors(N1[j]);
  temp2 := rewritefactors(N2[j]);
  temp4 := rewritefactors(N4[j]);
  temp5 := rewritefactors(N5[j]);
  temp7 := rewritefactors(N7[j]);
  temp8 := rewritefactors(N8[j]); 
 
  print temp1;
  print 0;
  print temp2;
  print 0;
  print temp4;
  print 0;  
  print temp5;
  print 0;
  print temp7;
  print 0;  
  print temp8;

  return 0;
end function;


//Print outputs. Note the we use i-1 since Magma arrays start from 1, not 0.
for i in [1..27] do
  print i-1,base3(i-1),out(i);
end for;

//-------------------------------------------------------------------------------------------------------------------
//Magma code to count F_3(n,0,0,0). //Compare L000 with Maple worksheet F3(n,t1,t2,t3)Verify. Matches for (n,3) = 1.

//n should be at least 3
count000 := function( n );

F := GF(3^n);
P<x> := PolynomialRing(F);

L1 := [];

for a in F do

      b := &*[x - a^(3^i):i in [0..n-1]];

c := Eltseq(b);

if (c[n] eq 0) and (c[n-1] eq 0) and (c[n-2] eq 0) then

  Append(~L1,b);

end if;

end for;

return #L1;
end function;

//----------------------------------------------------------------------------------------------------------------

L000 := [0,0,0];

for i in [4..14] do

  temp := count000( i );
  Append(~L000,temp);
  print i, temp;
  
end for;




