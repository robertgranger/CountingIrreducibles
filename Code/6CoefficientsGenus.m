//Magma code for determining the genus of the curves arising when 6 coefficients are prescribed
//-------------------------------------------------------------------------------------------------------------------------
//Setup

//This is for the L polynomials
P<X> := PolynomialRing(Integers());

//This is ambient space of the curves
F2 := GF(2);
A5<a0,a1,a2,a3,a4> := AffineSpace(F2,5);

//Binary expansion of input integer i, assumed to be 6 bits long.
base2 := function( i );
  out := [];
  tmp := i;
  for j in [1..6] do
    out[7-j] := tmp mod 2;
    tmp := (tmp - out[7-j]) div 2;
  end for;
  return out;
end function;

//-------------------------------------------------------------------------------------------------------------------------

//Need to define the trace forms, dependent on B := [B[1],B[2],B[3],B[4],B[5],B[6]] vector, so define as a function. 
//Tr[i] are T_(7-i)(x^2 + x + r0), i.e., the base elements for the linear combinations.
//Also has inputs r1,r2,r3 where T1(x) = r1, T1(x^3) = r2, T1(x^5) = r3.
forms := function( B, r0, r1, r2, r3 );
  Tr := [];
  Tr[1] := a3^3 + a3 + (r1 + r2)*(a2^3 + a2 + a1^3 + a1 + a0^7) + a1^5 + a1^3 + a0^11 + a0^7 + r0*r1 + r0*r2 + r1*r2 + r2*r3 
         + (r0*(a2^3 + a2 + a1^3 + a1 + a0^7 + r1 + r2 + r1*r2 + 1) + r1 + r2 + r3)*B[2] + (r0*r1 + r0*r3 + r1)*B[3] 
         + r0*(r1 + r2)*B[4] + r0*B[6]; 
  Tr[2] := r0*(a2^3 + a2 + a1^3 + a1) + a0^9 + r0*a0^7 + (r1 + r2)*a0^5 + r1 + r2 + r1*r2 + r0*r1*r2 + (r0*a0^5 + r0*r2)*B[2] 
         + (r0*r1 + r0*r2)*B[3] + r0*B[5];
  Tr[3] := a2^3 + a2 + a1^3 + a1 + a0^7 + a0^5 + r0*r1 + r0*r2 + r1*r2 + r2 + (r0 + 1)*(r1 + r2)*B[2] + r0*B[4];
  Tr[4] := a0^5 + a0 + r0*(a0^3 + a0 + B[3]);
  Tr[5] := a0^3 + a0 + r0*B[2];
  Tr[6] := r0*B[1];
  return Tr;
end function;


//-------------------------------------------------------------------------------------------------------------------------
//This is the main function for 6 coefficients. i should be in [32..63] and n either 1,3,5 or 7 representing those n equal 
//to this mod 8. Values for T1(1),T2(1),T3(1),T4(1),T5(1),T6(1) depend on n mod 8. These are [B[1],B[2],B[3],B[4],B[5],B[6]].
outL6 := function( i, n );

  i2 := base2(i);

  if n eq 1 then 
    B := [1,0,0,0,0,0];
  elif n eq 3 then
    B := [1,1,1,0,0,0];
  elif n eq 5 then
    B := [1,0,0,1,1,0];
  elif n eq 7 then
    B := [1,1,1,1,1,1];
  end if;
 
  for r0 in F2 do
    for r1 in F2 do
      for r2 in F2 do
        for r3 in F2 do
        
          Tr := forms( B, r0, r1, r2, r3 );
          c1 := a1^2 + a1 + r1 + a0;
          c2 := a2^2 + a2 + r2 + a0^3;
          c3 := a3^2 + a3 + r3 + a0^5;
          c4 := a4^2 + a4 + &+[i2[j]*Tr[j]: j in [1..6]];
          I := ideal< CoordinateRing(A5) | c1,c2,c3,c4>; 
          C := Curve(A5,I);

          if Genus(C) ne 50 then
            print "Genus(C) is not 50";
          end if;       
            
        end for;
      end for;
    end for;
  end for;

  return i,n;
end function;

//----------------------------------------------------------------------------------------------------------------------------
//This verifies that all of the curves are reduced, irreducible and have genus 50.
for i in [32..63] do
  outL6(i,1);
  outL6(i,3);
  outL6(i,5);
  outL6(i,7);
end for; 




