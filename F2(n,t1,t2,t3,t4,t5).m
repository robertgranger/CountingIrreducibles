//------------------------------------------------------------------------------------------------------------------------------//
// Filename: F2(n,t1,t2,t3,t4,t5).m
//
// Purpose:  This magma code computes Z(i*f) for i in [0..31] and f = (T_5,T_4,T_3,T_2,T_1) for n = 1,3,5,7 (mod 8), and then 
// applies Transform 2 to give N(j) for j in [0..31].
//
// Date: 21st October 2016
// Author: Robert Granger		
//------------------------------------------------------------------------------------------------------------------------------//

//The following store the vector of Z(i*f) for i in [2..31] and n = 1,3,5,7 (mod 8). Note that we ignore Z(0*f) = 2^n 
//and Z(1*f) = 2^(n-1) and the first two columns of the matrix, and focus on the roots of the L-polynomials only. 
Z1 := [];
Z3 := [];
Z5 := [];
Z7 := [];

//--------------------------------------------------------------------------------------------------------------------------------

//Compute the relevant L-polynomials when the first 2 and 3 coefficients are prescribed, i.e., Z(i*f) for i in [2..7] and
//f = (T_3,T_2,T_1), and n = 1,3 (mod 4), or rather n = 1,3,5,7 (mod 8) via duplication.

//Notes:

//We combine 2 and 3 because they both only use two auxiliary variables to define the relevant curves.
//outL3 takes input i in [2..7] and n either 1 or 3, representing these residue classes mod 4 and returns the L-polynomial. 

//--------------------------------------------------------------------------------------------------------------------------------
//Setup

//This is for the L-polynomials
P<X> := PolynomialRing(Integers());

//This is ambient space of the curves
F2 := GF(2);
A2<a0,a1> := AffineSpace(F2,2);

//Binary expansion of input integer i, assumed to be 3 bits long.
base2 := function( i );
  out := [];
  tmp := i;
  for j in [1..3] do
    out[4-j] := tmp mod 2;
    tmp := (tmp - out[4-j]) div 2;
  end for;
  return out;
end function;

//----------------------------------------------------------------------------------------------------------------------------------

//Need to define the trace forms, dependent on B := [B[1],B[2],B[3]] vector, so define as a function. 
//Tr[i] is T_(4-i)(x^2 + x + r0), i.e., the base elements for the linear combinations.
forms := function( B, r0 );
  Tr := [];
  Tr[1] := a0^5 + a0 + r0*(a0^3 + a0 + B[3]);
  Tr[2] := a0^3 + a0 + r0*B[2];
  Tr[3] := r0*B[1];
  return Tr;
end function;


//This is the main function for 3 coefficients. i should be in [2..7] and n either 1 or 3, representing those n equal to this mod 4
//Values for T1(1),T2(1),T3(1) depend on n mod 4. These are B := [B[1],B[2],B[3]].
outL3 := function( i, n );

  i2 := base2(i);

  if n eq 1 then 
    B := [1,0,0];
  elif n eq 3 then
    B := [1,1,1];
  end if;

  L := 1;

  for r0 in F2 do
    Tr := forms( B, r0 );
    c1 := (a1^2 + a1) + &+[i2[j]*Tr[j]: j in [1..3]];
    I := ideal< CoordinateRing(A2) | c1>; 
    C := Curve(A2,I);
    L := L*P!LPolynomial(C);
  end for;
 
  //Power by 4 to account for the fact that there are 2 auxiliary variables used here, so we must divide by 2^2, whereas for
  //4 and 5 coefficients there are 4 auxiliary variables, at which point we must divide by 2^4. Note this is entirely separate 
  //from the denominator 16 of S_5.
  return ReciprocalPolynomial(L^4);
end function;

//Note that we repeat to go from mod 4 to mod 8
for i in [2..7] do
  Z1[i-1] := outL3(i,1);
  Z3[i-1] := outL3(i,3);
  Z5[i-1] := outL3(i,1);
  Z7[i-1] := outL3(i,3);
end for;

//--------------------------------------------------------------------------------------------------------------------------------
//Compute the relevant L-polynomials when the first 4 and 5 coefficients are prescribed, i.e., Z(i \cdot q) for i in [8..31] and
//f = (T_5,T_4,T_3,T_2,T_1), and n = 1,3,5,7 (mod 8).

//Notes:

//We combine 4 and 5 because they both use 4 auxiliary variables to define the relevant curves.
//The main function outL5 takes input i in [8..31] and n either 1,3,5 or 7 representing these residue classes mod 8 and returns 
//the L-polynomial L. 

//--------------------------------------------------------------------------------------------------------------------------------
//Setup

//This is for the L polynomials
P<X> := PolynomialRing(Integers());

//This is ambient space of the curves
F2 := GF(2);
A4<a0,a1,a2,a3> := AffineSpace(F2,4);

//Binary expansion of input integer i, assumed to be 5 bits long.
base2 := function( i );
  out := [];
  tmp := i;
  for j in [1..5] do
    out[6-j] := tmp mod 2;
    tmp := (tmp - out[6-j]) div 2;
  end for;
  return out;
end function;

//-------------------------------------------------------------------------------------------------------------------------------

//Need to define the trace forms, dependent on B := [B[1],B[2],B[3],B[4],B[5]] vector, so define as a function. 
//Tr[i] are T_(6-i)(x^2 + x + r0), i.e., the base elements for the linear combinations.
//Also has inputs r1,r2 where T1(x) = r1, T1(x^3) = r2.
forms := function( B, r0, r1, r2 );
  Tr := [];
  Tr[1] := r0*(a2^3 + a2 + a1^3 + a1) + a0^9 + r0*a0^7 + (r1 + r2)*a0^5 + r1 + r2 + r1*r2 + r0*r1*r2 + (r0*a0^5 + r0*r2)*B[2] 
         + (r0*r1 + r0*r2)*B[3] + r0*B[5];
  Tr[2] := a2^3 + a2 + a1^3 + a1 + a0^7 + a0^5 + r0*r1 + r0*r2 + r1*r2 + r2 + (r0 + 1)*(r1 + r2)*B[2] + r0*B[4];
  Tr[3] := a0^5 + a0 + r0*(a0^3 + a0 + B[3]);
  Tr[4] := a0^3 + a0 + r0*B[2];
  Tr[5] := r0*B[1];
  return Tr;
end function;


//This is the main function for 5 coefficients. i should be in [8..31] and n either 1,3,5 or 7 representing those n equal to 
//this mod 8.
//Values for T1(1),T2(1),T3(1),T4(1),T5(1) depend on n mod 8. These are [B[1],B[2],B[3],B[4],B[5]].
outL5 := function( i, n );

  i2 := base2(i);

  if n eq 1 then 
    B := [1,0,0,0,0];
  elif n eq 3 then
    B := [1,1,1,0,0];
  elif n eq 5 then
    B := [1,0,0,1,1];
  elif n eq 7 then
    B := [1,1,1,1,1];
  end if;
 
  L := 1;

  for r0 in F2 do
    for r1 in F2 do
      for r2 in F2 do

        Tr := forms( B, r0, r1, r2 );
        c1 := a1^2 + a1 + r1 + a0;
        c2 := a2^2 + a2 + r2 + a0^3;
        c3 := a3^2 + a3 + &+[i2[j]*Tr[j]: j in [1..5]];
        I := ideal< CoordinateRing(A4) | c1,c2,c3>; 
        C := Curve(A4,I);
        L := L*P!LPolynomial(C);

      end for;
    end for;
  end for;

  return ReciprocalPolynomial(L);
end function;


for i in [8..31] do
  Z1[i-1] := outL5(i,1); print Z1[i-1];
  Z3[i-1] := outL5(i,3); print Z3[i-1];
  Z5[i-1] := outL5(i,5); print Z5[i-1];
  Z7[i-1] := outL5(i,7); print Z7[i-1];
end for;

//----------------------------------------------------------------------------------------------------------------------------------

//This is 16 * S_5^(-1) with the first two columns deleted since all rows give a 2^(n-1) contribution. 
M := Matrix(32,30,[
[1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1],
[1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1],
[-1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1],
[-1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1],
[1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1],
[1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1],
[-1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1],
[-1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1],
[1 , 1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1],
[1 , -1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1],
[-1 , -1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1],
[-1 , 1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1],
[1 , 1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1],
[1 , -1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1],
[-1 , -1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1],
[-1 , 1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1],
[1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1],
[1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1],
[-1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1],
[-1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1],
[1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1],
[1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1],
[-1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1],
[-1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1],
[1 , 1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1],
[1 , -1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1],
[-1 , -1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1],
[-1 , 1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1],
[1 , 1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1],
[1 , -1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1],
[-1 , -1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , -1 , -1 , 1 , 1],
[-1 , 1 , -1 , 1 , 1 , -1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1 , 1 , -1 , -1 , 1 , 1 , -1 , -1 , 1 , -1 , 1 , 1 , -1]
]);

//--------------------------------------------------------------------------------------------------------------------------------------

//This computes the L-polynomial expressions for N(j) and Zn with n = 1,3,5,7 
computequo := function( j, Z );

  num := 1;
  den := 1;

  for k in [1..30] do
    if M[j,k] eq 1 then
      num := num*Z[k];
    else  
      den := den*Z[k];  
    end if;
  end for;

  return num/den;
end function;


//Computes the L-polynomial expressions for N(j) for j in [0..31], for n = 1 (mod 8). Remember that Magma arrays start from 1, not 0.
N1 := [];

//Compute N1[1] last in order to avoid a sequence mutation
for j in [2..32] do
  N1[j] := computequo(j, Z1);
  print j;
  Factorisation(Numerator(N1[j]));
  Factorisation(Denominator(N1[j]));
end for;

N1[1] := computequo(1, Z1);

//Computes the L-polynomial expressions for N(j) for j in [0..31], for n = 3 (mod 8).
N3 := [];

//Compute N3[1] last in order to avoid a sequence mutation
for j in [2..32] do
  N3[j] := computequo(j, Z3);
  print j;
  Factorisation(Numerator(N3[j]));
  Factorisation(Denominator(N3[j]));
end for;

N3[1] := computequo(1, Z3);

//Computes the L-polynomial expressions for N(j) for j in [0..31], for n = 5 (mod 8).
N5 := [];

//Compute N5[1] last in order to avoid a sequence mutation
for j in [2..32] do
  N5[j] := computequo(j, Z5);
  print j;
  Factorisation(Numerator(N5[j]));
  Factorisation(Denominator(N5[j]));
end for;

N5[1] := computequo(1, Z5);

//Computes the L-polynomial expressions for N(j) for j in [0..31], for n = 7 (mod 8).
N7 := [];

//Compute N7[1] last in order to avoid a sequence mutation
for j in [2..32] do
  N7[j] := computequo(j, Z7);
  print j;
  Factorisation(Numerator(N7[j]));
  Factorisation(Denominator(N7[j]));
end for;

N7[1] := computequo(1, Z7);

//---------------------------------------------------------------------------------------------------------------------------------
//Since many of the occurring irreducible factors f(X) equal g(-X) for other occurring factors, we cancel the cancelling roots and 
//combine those that do not.

//Running through the F(n,0,0,0,0,0) polynomials (worst case as no -1's in that row) the features ones are:
f := [];

f[1] := X^2 - 2*X + 2; //cancels with
f[2] := X^2 + 2*X + 2;

f[3] := X^2 - 2; //vanishes
f[4] := X^2 + 2; //vanishes

f[5] := X^4 - 2*X^3 + 2*X^2 - 4*X + 4; //cancels with
f[6] := X^4 + 2*X^3 + 2*X^2 + 4*X + 4;

f[7] := X^4 - 2*X^2 + 4; //vanishes
f[8] := X^4 + 2*X^2 + 4; //vanishes 

f[9] := X^8 - 4*X^7 + 6*X^6 - 4*X^5 + 2*X^4 - 8*X^3 + 24*X^2 - 32*X + 16; //cancels with
f[10] := X^8 + 4*X^7 + 6*X^6 + 4*X^5 + 2*X^4 + 8*X^3 + 24*X^2 + 32*X + 16;

f[11] := X^8 - 2*X^7 + 2*X^6 - 4*X^4 + 8*X^2 - 16*X + 16; //cancels with
f[12] := X^8 + 2*X^7 + 2*X^6 - 4*X^4 + 8*X^2 + 16*X + 16;

f[13] := X^8 + 16; //vanishes

f[14] := X^8 + 2*X^6 - 4*X^5 + 2*X^4 - 8*X^3 + 8*X^2 + 16; //cancels with
f[15] := X^8 + 2*X^6 + 4*X^5 + 2*X^4 + 8*X^3 + 8*X^2 + 16;

f[16] := X^8 + 2*X^6 + 4*X^4 + 8*X^2 + 16; //vanishes

f[17] := X^12 - 2*X^10 - 2*X^8 + 16*X^6 - 8*X^4 - 32*X^2 + 64; //vanishes
f[18] := X^12 - 2*X^10 + 6*X^8 - 8*X^6 + 24*X^4 - 32*X^2 + 64; //vanishes
f[19] := X^12 + 2*X^10 - 2*X^8 - 16*X^6 - 8*X^4 + 32*X^2 + 64; //vanishes
f[20] := X^12 + 2*X^10 + 6*X^8 + 8*X^6 + 24*X^4 + 32*X^2 + 64; //vanishes

f[21] := X^16 - 2*X^14 - 2*X^12 + 8*X^10 - 8*X^8 + 32*X^6 - 32*X^4 - 128*X^2 + 256; //vanishes
f[22] := X^16 - 2*X^14 + 6*X^12 - 16*X^10 + 24*X^8 - 64*X^6 + 96*X^4 - 128*X^2 + 256; //vanishes
f[23] := X^16 + 2*X^14 - 2*X^12 - 8*X^10 - 8*X^8 - 32*X^6 - 32*X^4 + 128*X^2 + 256; //vanishes
f[24] := X^16 + 2*X^14 + 6*X^12 + 16*X^10 + 24*X^8 + 64*X^6 + 96*X^4 + 128*X^2 + 256; //vanishes


//This function rewrites an input poly over the factors of f[], with exponents, allowing for cancellations, and denominators.
//Input is N1[j] = num/den
rewritefactors := function( quo );

  num := Numerator(quo);
  den := Denominator(quo);

  Facnum := Factorisation(num);
  Facden := Factorisation(den);


  temp1 := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
  for i in [1..#Facnum] do
    temp1[Index(f,Facnum[i][1])] := Facnum[i][2];
  end for;

  temp2 :=[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
  for i in [1..#Facden] do
    temp2[Index(f,Facden[i][1])] := Facden[i][2];
  end for;

  temp := [];
  for i in [1..24] do
    temp[i] := temp1[i] - temp2[i];
  end for;

  //this will be the output vector of exponents of the f[i]
  expvec := [];

  if temp[1] ge temp[2] then
    expvec[1] := temp[1] - temp[2]; 
    expvec[2] := 0;
  else 
    expvec[1] := 0; 
    expvec[2] := temp[2] - temp[1];
  end if;

  expvec[3] := 0;
  expvec[4] := 0;

  if temp[5] ge temp[6] then
    expvec[5] := temp[5] - temp[6]; 
    expvec[6] := 0;
  else 
    expvec[5] := 0; 
    expvec[6] := temp[6] - temp[5];
  end if;

  expvec[7] := 0;
  expvec[8] := 0;

  if temp[9] ge temp[10] then
    expvec[9] := temp[9] - temp[10]; 
    expvec[10] := 0;
  else 
    expvec[9] := 0; 
    expvec[10] := temp[10] - temp[9];
  end if;

  if temp[11] ge temp[12] then
    expvec[11] := temp[11] - temp[12]; 
    expvec[12] := 0;
  else 
    expvec[11] := 0; 
    expvec[12] := temp[12] - temp[11];
  end if;

  expvec[13] := 0;

  if temp[14] ge temp[15] then
    expvec[14] := temp[14] - temp[15]; 
    expvec[15] := 0;
  else 
    expvec[14] := 0; 
    expvec[15] := temp[15] - temp[14];
  end if;

  expvec[16] := 0;
  expvec[17] := 0;
  expvec[18] := 0;
  expvec[19] := 0;
  expvec[20] := 0;
  expvec[21] := 0;
  expvec[22] := 0;
  expvec[23] := 0;
  expvec[24] := 0;

  return Factorisation( &*[f[i]^expvec[i]: i in [1..#f]] );
end function;


//----------------------------------------------------------------------------------------------------------------------------

//Output function for latex. Input is N[j].

//Note that we must divide the exponents by 2^4, since there are 4 variables. We must also divide by 16, since this is the 
//denominator of the matrix. However, since we shall make the coefficient 1/2^5 (for 5 coefficients), we multiply by 2 as well, 
//so in the following we only divide by 8.


//This is a subroutine for the ensuing function
subout := function( tempin );

/*
f1,f2 // -, +       p_2
f5,f6  // - , +     p_4
f9,f10  // - , +   p_{8,1}
f11,f12 // - , +  p_{8,3}
f14,f15 // -, +   p_{8,2}
*/

  out := [0,0,0,0,0];

  if tempin[1][1] eq f[1] then 
    out[1] := -tempin[1][2] div 8;
  elif tempin[1][1] eq f[2] then 
    out[1] := tempin[1][2] div 8;
  end if;

  if tempin[2][1] eq f[5] then 
    out[2] := -tempin[2][2] div 8;
  elif tempin[2][1] eq f[6] then 
    out[2] := tempin[2][2] div 8;
  end if;

  test := Index(f,tempin[3][1]);
  if test eq 9 then
    out[3] := -tempin[3][2] div 8;
  elif test eq 10 then
    out[3] := tempin[3][2] div 8;
  elif test eq 11 then
    out[5] := -tempin[3][2] div 8;
  elif test eq 12 then
    out[5] := tempin[3][2] div 8;
  elif test eq 14 then
    out[4] := -tempin[3][2] div 8;
  elif test eq 15 then
    out[4] := tempin[3][2] div 8;
  end if;

  test := Index(f,tempin[4][1]);
  if test eq 9 then
    out[3] := -tempin[4][2] div 8;
  elif test eq 10 then
    out[3] := tempin[4][2] div 8;
  elif test eq 11 then
    out[5] := -tempin[4][2] div 8;
  elif test eq 12 then
    out[5] := tempin[4][2] div 8;
  elif test eq 14 then
    out[4] := -tempin[4][2] div 8;
  elif test eq 15 then
    out[4] := tempin[4][2] div 8;
  end if;

  return out;
end function;


//This is the output function
out := function( j );
  temp1 := rewritefactors(N1[j]);
  temp3 := rewritefactors(N3[j]);
  temp5 := rewritefactors(N5[j]);
  temp7 := rewritefactors(N7[j]);
  out1 := subout( temp1 );
  out3 := subout( temp3 );
  out5 := subout( temp5 );
  out7 := subout( temp7 );
  print out1[1], "r_n(p_2)+", out1[2],  "r_n(p_4)+",  out1[3],  "r_n(p_{8,1})+", out1[4],  "r_n(p_{8,2})+", out1[5],  "r_n(p_{8,3}) & \ \text{if} \ n   \equiv 1 \pmod{8}\\";  
  print out3[1], "r_n(p_2)+", out3[2],  "r_n(p_4)+",  out3[3],  "r_n(p_{8,1})+", out3[4],  "r_n(p_{8,2})+", out3[5],  "r_n(p_{8,3}) & \ \text{if} \ n \equiv 3 \pmod{8}\\";  
  print out5[1], "r_n(p_2)+", out5[2],  "r_n(p_4)+",  out5[3],  "r_n(p_{8,1})+", out5[4],  "r_n(p_{8,2})+", out5[5],  "r_n(p_{8,3}) & \ \text{if} \ n \equiv 5 \pmod{8}\\";  
  print out7[1], "r_n(p_2)+", out7[2],  "r_n(p_4)+",  out7[3],  "r_n(p_{8,1})+", out7[4],  "r_n(p_{8,2})+", out7[5],  "r_n(p_{8,3}) & \ \text{if} \ n \equiv 7 \pmod{8}\\"; 
  return out1,out3,out5,out7;
end function;

//Print outputs. Note the we use i-1 since Magma arrays start from 1, not 0.
for i in [1..32] do
  print i-1,base2(i-1),out(i);
end for;
