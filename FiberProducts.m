//////////////////////////////////////////////////////////////////////////////////
//// Loading packages ////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

// To determine the nonsurjective primes associated with a non-CM elliptic curve,
// we use the `GL2EllAdicImages` function from the "ell-adic-galois-images"
// repository by Rouse, Sutherland, and Zureick-Brown.
ChangeDirectory(".../ell-adic-galois-images-main"); // Modify this path as needed.
Attach("groups/gl2.m");
load "groups/gl2data.m";
RSZB := GL2Load(0);

// To obtain better models for certain modular curves, we use the `FindModelOfXG` 
// function from Zywina's "FindOpenImage" repository. We also use `PointsViaLifting`
// from the same repository for checking whether such curves have points locally.
ChangeDirectory(".../OpenImage-master");  // Modify this path as needed.
load "main/GL2GroupTheory.m";
load "main/ModularCurves.m";

//////////////////////////////////////////////////////////////////////////////////
//// Initializing j-maps /////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

// We create an associative array `jMaps` in which the keys are labels (RSZB or 
// common names) for modular curves X_H. The corresponding values are rational
// functions defining the j-map j: X_H -> P^1(Q). These are sourced from "Modular
// curves of prime-power level with infinitely many rational points" by Sutherland 
// and Zywina, except for X0(10), which is taken from "On the field of definition 
// of p-torsion points on elliptic curves over the rationals" by Lozano-Robledo.
InitializejMaps := function()
    R<t> := FunctionField(Rationals());
    jMaps := AssociativeArray();
    jMaps["Xns(2)"]   := t^2+1728;
    jMaps["X0(2)"]    := (256-t)^3/t^2;
    jMaps["Xns+(3)"]  := t^3;
    jMaps["X0(3)"]    := (t+3)^3*(t+27)/t;
    jMaps["4.2.0.1"]  := -t^2 + 1728;
    jMaps["Xns+(4)"]  := 4*t^3*(8-t);
    jMaps["XS4(5)"]   := t^3*(t^2+5*t+40);
    jMaps["X0(5)"]    := (t^2+10*t+5)^3/t;
    jMaps["Xns+(5)"]  := 8000*t^3*(t+1)*(t^2-5*t+10)^3/(t^2-5)^5;
    jMaps["Xsp+(5)"]  := Evaluate(t^3*(t^2+5*t+40),(t+5)*(t^2-5)/(t^2+5*t+5));
    jMaps["8.2.0.1"]  := -2*t^2+1728;
    jMaps["8.2.0.2"]  := 2*t^2+1728;
    jMaps["9.27.0.1"] := 3^7*(t^2-1)^3*(t^6+3*t^5+6*t^4+t^3-3*t^2+12*t+16)^3*(2*t^3+3*t^2-3*t-5)/(t^3-3*t-1)^9;
    jMaps["X0(10)"]   := (t^6-4*t^5+16*t+16)^3/((t+1)^2*(t-4)*t^5);
    return jMaps;
end function;

jMaps := InitializejMaps();

//////////////////////////////////////////////////////////////////////////////////
//// Helper functions ////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

// Given j-maps j1: X_{H_1} -> P^1(Q) and j2: X_{H_2} -> P^1(Q), construct a model 
// C for the fiber product X_{H_1} x X_{H_2} using the method of Example 4, along 
// with the induced j-map j: C -> P^1(Q). Note that C is often singular.
ConstructFiberProduct := function(j1, j2)
    F := FunctionField(Rationals(), 2);
    f := Numerator(Evaluate(j1, F.1) - Evaluate(j2, F.2));
    C := ProjectiveClosure(Curve(AffineSpace(Rationals(), 2), f));
    j := FunctionField(C)!Evaluate(j1, C.1/C.3);
    return C, j;
end function;

// Given the set `RatPlaces` of all rational places on a curve C and `j`, the j-
// map j: C -> P^1(Q), print for each rational place: the j-invariant, whether it 
// corresponds to a CM elliptic curve, and the nonsurjective primes if non-CM.
AnalyzePlaces := procedure(RatPlaces, j)
    if IsEmpty(RatPlaces) then
        print "This curve has no rational places.";
    else
        printf "%-30o %-14o %-8o %-10o\n", "Rational places", "j-invariant", "Has CM", "Nonsurjective primes";
        for pl in RatPlaces do
            jinv := Evaluate(j, pl);
            HasCM := "---";
            NonSurjPrimes := "---";
            if jinv ne Infinity() then
                Ej := EllipticCurveFromjInvariant(jinv);
                HasCM := HasComplexMultiplication(Ej);
                if not HasCM then
                    NonSurjPrimes := {Factorization(StringToInteger(Split(lbl, ".")[1]))[1][1] : lbl in GL2EllAdicImages(Ej,RSZB)};
                end if;
            end if;
            printf "%-30o %-14o %-8o %-10o\n", pl, jinv, HasCM, NonSurjPrimes;
        end for;
    end if;
end procedure;

// Given a set `RatPts` of rational points on a curve, return the set of all
// rational places lying above each point in `RatPts`.
RationalPlaces := function(RatPts)
    return &join{ {pl : pl in Places(pt) | Degree(pl) eq 1} : pt in RatPts };
end function;

// Given a curve `C` that is birational to an elliptic curve of rank 0, return the 
// provably complete set of rational places on `C`. The parameter `BasePoint` must 
// lie on `C` and defaults to (0:1:0), which is often (but not always) a point on 
// the curves to which we will apply this function.
RationalPlacesGenus1 := function(C : BasePoint := [0,1,0])
    error if Genus(C) ne 1, "Curve must be genus 1.";
    error if not BasePoint in C, "BasePoint must lie on the curve.";
    E, phi := EllipticCurve(C, C!BasePoint);
    error if Rank(E) ne 0, "Elliptic curve must have rank 0.";
    T, psi := TorsionSubgroup(E);
    RatPts := &join{ {C!P : P in RationalPoints(psi(Q) @@ phi)} : Q in T };
    return RationalPlaces(RatPts);
end function;

// Given a curve `C` that is birational to a nice genus 2 curve whose Jacobian has 
// rank 0, return the provably complete set of rational places on `C`. This 
// function uses Magma's `Chabauty0` command.
RationalPlacesGenus2 := function(C)
    error if Genus(C) ne 2, "Curve must be genus 2.";
    chk, H, phi1 := IsHyperelliptic(C);
    assert chk;
    HSimp, phi2 := SimplifiedModel(H);
    Jac := Jacobian(HSimp);
    r1, r2 := RankBounds(Jac);
    error if <r1, r2> ne <0, 0>, "Jacobian must have rank 0.";
    RatPts := &join{ {C!P : P in RationalPoints((Q @@ phi2) @@ phi1)} : Q in Chabauty0(Jac) };
    return RationalPlaces(RatPts);
end function;

//////////////////////////////////////////////////////////////////////////////////
//// Tree with root X0(3) ////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

// X0(3) x XS4(5): Genus 1 rank 0
C, j := ConstructFiberProduct(jMaps["X0(3)"], jMaps["XS4(5)"]);
AnalyzePlaces(RationalPlacesGenus1(C), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place at (-81 : -13 : 1)       -316368        false    { 2, 3, 5 }
// Place at (0 : 1 : 0)           Infinity       ---      ---
// Place at (1 : 0 : 0)           Infinity       ---      ---
// Place at (-27 : 0 : 1)         0              true     ---
// Place at (-9 : 2 : 1)          432            false    { 2, 3, 5 }

// X0(3) x X0(5) = X0(15): Genus 1 rank 0
C, j := ConstructFiberProduct(jMaps["X0(3)"], jMaps["X0(5)"]);
AnalyzePlaces(RationalPlacesGenus1(C), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place at (0 : 0 : 1)           Infinity       ---      ---
// Place at (-32 : -25/2 : 1)     -121945/32     false    { 2, 3, 5 }
// Place at (-2 : -10 : 1)        -25/2          false    { 2, 3, 5 }
// Place (1) at (1 : 0 : 0)       Infinity       ---      ---
// Place (2) at (1 : 0 : 0)       Infinity       ---      ---
// Place at (0 : 1 : 0)           Infinity       ---      ---
// Place at (-729/32 : -25/8 : 1) 46969655/32768 false    { 2, 3, 5 }
// Place at (-729/2 : -40 : 1)    -349938025/8   false    { 2, 3, 5 }

// X0(3) x Xns+(5): Genus 2 rank 0
C, j := ConstructFiberProduct(jMaps["X0(3)"], jMaps["Xns+(5)"]);
AnalyzePlaces(RationalPlacesGenus2(C), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place at (-3 : -1 : 1)         0              true     ---
// Place at (27 : 3 : 1)          54000          true     ---
// Place at (-243 : 2 : 1)        -12288000      true     ---
// Place at (-27 : -1 : 1)        0              true     ---
// Place at (-27 : 0 : 1)         0              true     ---

//////////////////////////////////////////////////////////////////////////////////
//// Tree with root 9.27.0.1 /////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

// 9.27.0.1 x Xns(2): No 3-adic points
C, j := ConstructFiberProduct(jMaps["9.27.0.1"], jMaps["Xns(2)"]);
chk, H, phi := IsHyperelliptic(C);
assert chk;
IsLocallySolvable(H, 3); // Prints false, which indicates no 3-adic points

// 9.27.0.1 x X0(2): No 3-adic points
C, j := ConstructFiberProduct(jMaps["9.27.0.1"], jMaps["X0(2)"]);
assert not IsHyperelliptic(C);
phi := CanonicalMap(C);
H := CanonicalImage(C, phi);
IsLocallySolvable(H, 3); // Prints false, which indicates no 3-adic points

// 9.27.0.1 x 4.2.0.1: No 3-adic points
C, j := ConstructFiberProduct(jMaps["9.27.0.1"], jMaps["4.2.0.1"]);
chk, H, phi := IsHyperelliptic(C);
assert chk;
IsLocallySolvable(H, 3); // Prints false, which indicates no 3-adic points

// 9.27.0.1 x Xns+(4) x XS4(5): Covers 9.27.0.1 x XS4(5), which has no 3-adic points
G92701 := sub<GL(2, Integers(9)) | [[4, 2, 3, 7], [6, 7, 1, 3]]>;
GXS45 := sub<GL(2, Integers(5)) | [[1, 2, 2, 0], [2, 0, 2, 4]]>;
lvl := 9 * 5;
G := gl2Lift(G92701, lvl) meet gl2Lift(GXS45, lvl);
X := CreateModularCurveRec(lvl, Generators(G));
PointsViaLifting(FindModelOfXG(X,30)`psi, 3, 2); // Prints {}, which indicates no points mod 3^2

// 9.27.0.1 x Xns+(4) x X0(5): Covers 9.27.0.1 x X0(5), which has no 3-adic points
G92701 := sub<GL(2, Integers(9)) | [[4, 2, 3, 7], [6, 7, 1, 3]]>;
GX05 := sub<GL(2, Integers(5)) | [[2, 2, 0, 1], [3, 4, 0, 3]]>;
lvl := 9 * 5;
G := gl2Lift(G92701, lvl) meet gl2Lift(GX05, lvl);
X := CreateModularCurveRec(lvl, Generators(G));
PointsViaLifting(FindModelOfXG(X,30)`psi, 3, 2); // Prints {}, which indicates no points mod 3^2

// 9.27.0.1 x Xns+(4) x Xns+(5): Covers Xns+(4) x Xns+(5), whose rational points
// have been determined in the literature; see our paper for citations.

// 9.27.0.1 x 8.2.0.1: No 3-adic points
C, j := ConstructFiberProduct(jMaps["9.27.0.1"], jMaps["8.2.0.1"]);
chk, H, phi := IsHyperelliptic(C);
assert chk;
IsLocallySolvable(H, 3); // Prints false, which indicates no 3-adic points

// 9.27.0.1 x 8.2.0.2: No 3-adic points
C, j := ConstructFiberProduct(jMaps["9.27.0.1"], jMaps["8.2.0.2"]);
chk, H, phi := IsHyperelliptic(C);
assert chk;
IsLocallySolvable(H, 3); // Prints false, which indicates no 3-adic points

//////////////////////////////////////////////////////////////////////////////////
//// Tree with root Xns+(3) //////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

// Xns+(3) x Xns(2): Genus 1 rank 0
C, j := ConstructFiberProduct(jMaps["Xns+(3)"], jMaps["Xns(2)"]);
AnalyzePlaces(RationalPlacesGenus1(C), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place at (12 : 0 : 1)          1728           true     ---
// Place at (0 : 1 : 0)           Infinity       ---      ---

// Xns+(3) x X0(2) x XS4(5): Covers X0(2) x XS4(5), which is genus 1 rank 0
C, j := ConstructFiberProduct(jMaps["X0(2)"], jMaps["XS4(5)"]);
AnalyzePlaces(RationalPlacesGenus1(C), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place at (1 : 0 : 0)           Infinity       ---      ---
// Place at (0 : 1 : 0)           Infinity       ---      ---
// Place at (64 : 3 : 1)          1728           true     ---
// Place at (-8 : 11 : 1)         287496         true     ---
// Place at (-512 : 3 : 1)        1728           true     ---

// Xns+(3) x X0(2) x X0(5) = Xns+(3) x X0(10): Genus 2 rank 0
C, j := ConstructFiberProduct(jMaps["Xns+(3)"], jMaps["X0(10)"]);
AnalyzePlaces(RationalPlacesGenus2(C), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place (1) at (1 : 0 : 0)       Infinity       ---      ---
// Place (2) at (1 : 0 : 0)       Infinity       ---      ---
// Place (3) at (1 : 0 : 0)       Infinity       ---      ---
// Place (4) at (1 : 0 : 0)       Infinity       ---      ---

// Xns+(3) x X0(2) x Xns+(5): Covers X0(2) x Xns+(5), which is genus 1 rank 0
C, j := ConstructFiberProduct(jMaps["X0(2)"], jMaps["Xns+(5)"]);
AnalyzePlaces(RationalPlacesGenus1(C), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place at (1 : -3 : 1)          16581375       true     ---
// Place (1) at (0 : 1 : 0)       8000           true     ---
// Place at (16 : 3 : 1)          54000          true     ---
// Place at (4096 : 1 : 1)        -3375          true     ---
// Place at (256 : -1 : 1)        0              true     ---

// Xns+(3) x 4.2.0.1: Genus 1 rank 0
C, j := ConstructFiberProduct(jMaps["Xns+(3)"], jMaps["4.2.0.1"]);
AnalyzePlaces(RationalPlacesGenus1(C), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place at (12 : 0 : 1)          1728           true     ---
// Place at (0 : 1 : 0)           Infinity       ---      ---

// Xns+(3) x Xns+(4) x XS4(5): Covers Xns+(3) x XS4(5), whose rational points
// arise from those on Xns+(4) x Xsp+(5) by "curious group" considerations.
// The curve Xns+(4) x Xsp+(5) is a genus 3 plane quartic, which admits a map
// to an elliptic curve of rank 0 (which we find by taking a quotient).
C, j := ConstructFiberProduct(jMaps["Xns+(4)"], jMaps["Xsp+(5)"]);
P := AmbientSpace(C);
assert not IsHyperelliptic(C);
// 1. Compute the canonical image, which is a smooth plane quartic.
Can := CanonicalMap(C);
CanIm := CanonicalImage(C, Can);
// Simplify the model of the canonical image.
HPols, Mat := MinimizeReducePlaneQuartic(DefiningEquation(CanIm));
H := Curve(P, HPols);
// 2. Work out the maps.
// 2a. Map from H back to CanIm
polyseq := [ &+[ Mat[i][j]*H.j : j in [1,2,3] ] : i in [1,2,3] ];
HtoCan := map<H -> CanIm | polyseq>;
// 2b. Map from CanIm back to C
Can2 := map<C -> CanIm | DefiningPolynomials(Can)>;
chk, Can2inv := IsInvertible(Can2); // Takes about 1 minute
assert chk;
// 3. Find automorphism group of H and take quotient by order 2 automorphism.
A, phi := AutomorphismGroupOfPlaneQuartic(H : explicit := true);
M := phi(A.1);
autpolys := [ &+[ M[j][i] * P.i : i in [1,2,3] ] : j in [1,2,3] ];
aut := iso<H -> H | autpolys, autpolys>;
A := AutomorphismGroup(H, [aut]);
X, quomap := CurveQuotient(A);
// 4. Construct an elliptic curve birational to the quotient.
E0, ecmap := EllipticCurve(X, quomap(H!Random(Points(H))));
E, ecmap2 := MinimalModel(E0);
bigmap := Extend(Expand(quomap*ecmap*ecmap2));
// Find all rational points on H by pulling back points on E.
assert Rank(E) eq 0;
T, torsmap := TorsionSubgroup(E);
torspoints := [ torsmap(t) : t in T ];
allpoints := &join [ RationalPoints(torspoints[i]@@bigmap) : i in [1..#torspoints]];
// Map the points back to C and analyze.
RatPls := RationalPlaces({ (HtoCan*Can2inv)(p) : p in allpoints });
AnalyzePlaces(RatPls, j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place at (24 : -1 : 1)         -884736        true     ---
// Place at (-8 : -3 : 1)         -32768         true     ---
// Place (2) at (1 : 0 : 0)       Infinity       ---      ---
// Place at (-561/8 : -5/4 : 1)   -110349050625/1024 false    { 2, 5 }
// Place at (6 : -2 : 1)          1728           true     ---
// Place at (8 : -5 : 1)          0              true     ---

// Xns+(3) x Xns+(4) x X0(5): Covers Xns+(4) x X0(5), which is genus 1 rank 0
C, j := ConstructFiberProduct(jMaps["Xns+(4)"], jMaps["X0(5)"]);
AnalyzePlaces(RationalPlacesGenus1(C : BasePoint := [1,0,0]), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place (1) at (1 : 0 : 0)       Infinity       ---      ---
// Place (2) at (1 : 0 : 0)       Infinity       ---      ---
// Place at (59/8 : -25/4 : 1)    1026895/1024   false    { 2, 5 }
// Place at (41/2 : -20 : 1)      -1723025/4     false    { 2, 5 }

// Xns+(3) x Xns+(4) x Xns+(5): Covers Xns+(4) x Xns+(5), whose rational points
// have been determined in the literature; see our paper for citations.

// Xns+(3) x 8.2.0.1: Genus 1 rank 0
C, j := ConstructFiberProduct(jMaps["Xns+(3)"], jMaps["8.2.0.1"]);
AnalyzePlaces(RationalPlacesGenus1(C), j);
// Rational places                j-invariant    Has CM   Nonsurjective primes
// Place at (12 : 0 : 1)          1728           true     ---
// Place at (0 : 1 : 0)           Infinity       ---      ---

// Xns+(3) x 8.2.0.2: This is a "curious group." Its rational points arise from 
// rational points on Xns+(3) x X0(2), which has already been considered.
