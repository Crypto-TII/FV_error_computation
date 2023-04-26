function CL(ci,q)
// CL computed ci mod q in (-q/2,q/2]
    bound := q div 2;   // integer division
    ci := ci mod q;
    if ci gt bound then
        ci := ci - q;
    end if;
    return ci; 
    end function;

function cl(R,c,q)
// cl applies CL to all the coefficients of the polynomial c
    return R![CL(ci,q): ci in Coefficients(c)];
    end function;

function add(R,a,b,q)
// add performs the sum of two polynomials in Rq
    return cl(R,a+b,q);
    end function;

function mult(R,a,b,q)
// mult performs the mult of two polynomials in Rq
    return cl(R,a*b,q);
    end function;

function myRound(x)
// round to the closest integer
    //myRound(z) = 0 if z in (-0.5,0.5]
    y := Round(x);
    if (y-x) eq 0.5 then
        return y-1;
    end if;
    return y;
    end function;

function round(R,x,t)
// applies myRound to the coefficients of the polynomial x divided by t
    return R![myRound(ci/t): ci in Coefficients(x)];
    end function;

function genDG(sigma)
// generates the sequence PE, used in DG to generate elements from a discete gaussian
    PP := [RealField()!1];
    sum := 1;
    i := 1;
    px := Exp(-i^2/(2*sigma^2));
    sum := sum +2*px;
    while px/sum gt 10^(-20) do
        Append(~PP,px);
        Insert(~PP,1,px);
        i := i+1;
        px := Exp(-i^2/(2*sigma^2));
        sum := sum +2*px;
        end while;
    for j in [1..2*i-1] do
        PP[j] := PP[j]/sum;
        end for;
    PE := [&+PP[1..i]: i in [1..#PP]];
    dist := PE[1];
    for i in [2..#PE] do
        d := Abs(PE[i]-PE[i-1]);
        if d gt 0 then
            dist := Min(dist,d);
            end if;
    end for;
    return PE, -Floor(Log(10,dist))+1;
    end function;
    

function DG(PE,logdist)
// generates a random element from the discrete gaussian distribution
    esp := 10^logdist;
    x := Random(esp)/esp; //che i random lo siano davvero
    pos := 1;
    while x gt PE[pos] do
        pos := pos + 1;
    end while;
    return Integers()! (pos - Integers()!((#PE+1)/2));
    end function;

function chiErr(R,d,PE,logdist)
// generates a polynomial whose coefficients are sampled independently from the discrete gaussian
    return R![DG(PE,logdist): i in [1..d]];
    end function;

function chiKey(R,d)
// generates a polynomial with coefficients sampled independently from the key distribution (ternary)
    return R![Random([1,0,-1]): i in [1..d]];
    end function;

function unif(R,d,Zq)
// generates a polynomial with coefficients sampled independently from the uniform distribution over q
    return R![Random(Zq): i in [1..d]];
    end function;

function keyGen(R,d,PE,logdist,Q,Zq)
// performs the key generation sampling s, a and e, then computing b
// returns the secret key s, a and b
    s := chiKey(R,d);
    a := unif(R,d,Zq);
    e := chiErr(R,d,PE,logdist);
    b := add(R,-mult(R,a,s,Q),e,Q); //[-a*s + e]_Q
    return s, a, b;
    end function;

function kgGHS(R,d,PE,logdist,P,PQ,Zpq,s)
// performs the key switching key generation
    a2 := unif(R,d,Zpq);
    e2 := chiErr(R,d,PE,logdist);
    b2 := add(R,add(R,P*mult(R,s,s,PQ),mult(R,-a2,s,PQ),PQ),e2,PQ);
    return a2, b2;
    end function;

function encr(R,d,PE,logdist,m,t,Q,a,b)
// performs the encryption phase
    u := chiKey(R,d);
    e0 := chiErr(R,d,PE,logdist);
    e1 := chiErr(R,d,PE,logdist);
    return [add(R,add(R,round(R,Q*m,t),mult(R,u,b,Q),Q),e0,Q), add(R,mult(R,u,a,Q),e1,Q)];
    end function;

function decr(R,c,t,Q,s)
// decrypts a ciphertext c encrypted in mod Q
    return cl(R,round(R,t*add(R,c[1],mult(R,c[2],s,Q),Q),Q),t);
    end function;

function homAdd(R,c1,c2,Q)
// performs homomorphic addition between the ciphertexts c1 and c2
    return [add(R,c1[1],c2[1],Q),add(R,c1[2],c2[2],Q)];
    end function;

function homAdd2(R,c1,c2,Q)
// performs the homomorphic addition between the extended ciphertexts (in R_Q^3)
    return [add(R,c1[1],c2[1],Q),add(R,c1[2],c2[2],Q),add(R,c1[3],c2[3],Q)];
    end function;

function modSwitch(R,c,Q,P)
// performs the modulo switch from Q to P on the ciphertext c
    return [cl(R,round(R,P*c[k],Q),P): k in [1,2]];
    end function;

function homMult(R,c1,c2,t,Q,P,PQ)
// performs the homomorphic multiplication (as in paper Paper 2021/204 by Kim and al)
    c1p := modSwitch(R,c1,Q,P);
    return [cl(R,round(R,t*mult(R,c1p[1],c2[1],PQ),P),Q), cl(R,round(R,t*add(R,mult(R,c1p[1],c2[2],PQ),mult(R,c1p[2],c2[1],PQ),PQ),P),Q), cl(R,round(R,t*mult(R,c1p[2],c2[2],PQ),P),Q)];
    end function;

function relinGHS(R,cten,Q,P,PQ,a2,b2)
// performs the GHS kwy switch
    c0 := add(R,cten[1],round(R,mult(R,cten[3],b2,PQ),P),Q);
    c1 := add(R,cten[2],round(R,mult(R,cten[3],a2,PQ),P),Q);
    return [c0,c1];
    end function;

function oneLev2(R,eta,m,c,t,Q,P,PQ,a2,b2)
// generates 2 * eta plaintext, encrypts them and performs the first level of a Base Model circuit with no constant multiplications (eta additions, 1 multiplication with relinearization)
// returns the message obtained in clear (working only with plaintexts) and encrypted (working homomorphically with the ciphertexts)
    m1 := 0;
    m2 := 0;
    c1 := [R!0,0];
    c2 := [R!0,0];
    for i in [1..eta] do
        m1 := add(R,m1,m[i],t);
        m2 := add(R,m2,m[eta+i],t);
        c1 := homAdd(R,c1,c[i],Q);
        c2 := homAdd(R,c2,c[eta+i],Q);
    end for;
    return mult(R,m1,m2,t), relinGHS(R,homMult(R,c1,c2,t,Q,P,PQ),Q,P,PQ,a2,b2);
    end function;

function finalmcN(R,L,d,PE,logdist,eta,ell,len,t,Q,P,PQ,Zt,a,b,a2,b2)
// performs a Base Model circuit of multiplicative depth L-1, applying oneLev2 recursively
    if ell eq L-1 then
        m := [R![Random(Zt): j in [1..d]]: i in [1..len]];
        c := [encr(R,d,PE,logdist,m[i],t,Q,a,b): i in [1..len]];
        return oneLev2(R,eta,m,c,t,Q,P,PQ,a2,b2);
    end if;
    M := [R!0: i in [1..len]];
    C := [[R!0,0]: i in [1..len]];
    for i in [1..len] do
        M[i], C[i] := finalmcN(R,L,d,PE,logdist,eta,ell+1,len,t,Q,P,PQ,Zt,a,b,a2,b2);
    end for;
    return oneLev2(R,eta,M,C,t,Q,P,PQ,a2,b2);
    end function;

function genP(t,Q)
// generates P of approximately the same size of Q (coprime with t and Q)
    P := Random(Q,Q+500);
    while (Gcd(P,Q) ne 1 or Gcd(P,t) ne 1) do
        P := Random(Q,Q+500);
    end while;
    return P;
    end function;

function f(iota, d)
// computes the function f of our paper
    a := [0.2417, 0.2240, 0.2058, 0.1906];
    b := [2.3399, 2.4181, 2.4844, 2.5489];
    c := [8.1603, 8.8510, 9.5691, 10.2903];
    if d eq 2^12 then
        index := 1;
        elif d eq 2^13 then
        index := 2;
        elif d eq 2^14 then
        index := 5;
        elif d eq 2^15 then
        index := 4;
        end if;
    return c[index] - 1 / Exp(a[index] * iota - b[index]);
    end function;


function genQ(L,t,d,D,eta,sigma)
// generates Q accordingly to our formula
    Vs := 2/3;
    Vu := 2/3;
    Ve := sigma^2;
    Bclean := t^2 * (1/12 + d * Ve * Vu + Ve + d * Ve * Vs);
    Bms := t^2 * (1 + d * Vs) / 12;
    A := eta * t^2 * d^2 * Vs / 6;
    C := t^2 * d^2 * Vs * Bms / 12;
    g := 1;
    for iota in [2..L] do
        g := g * f(iota, d);
        end for;
    if L eq 1 then
        Q := Floor(2 * D * (2 * Bclean)^0.5);
        else
        Q := Floor(2 * D * (2 * A^(L-2) * (A * Bclean + C) * g)^0.5);
        end if;
    Q := 2 * (Q div 2) + 1;
    if Gcd(t,Q) ne 1 then
        Q := Q + 2;
        end if;
    return Q;
    end function;

function noise(R,K,d,m,c,t,Q,s)
// computes the noise of a ciphertext c from c and the corresponding message m
    cs := add(R,c[1],mult(R,c[2],s,Q),Q);
    err := K!PolynomialRing(Rationals())!(t*cs)/Q-K!PolynomialRing(Rationals())!m;
    return err; 
    end function;

function noise2(R,K,d,m,c,t,Q,s)
// computes the noise of an extended ciphertext
    cs := add(R,add(R,c[1],mult(R,c[2],s,Q),Q),mult(R,c[3],mult(R,s,s,Q),Q),Q);
    err := K!PolynomialRing(Rationals())!(t*cs)/Q-K!PolynomialRing(Rationals())!m;
    return err; 
    end function;

function ninf(n)
// computes the infinite norm of the coefficients vector of the polynomial n
    return Max([Abs(Coefficients(n)[i]): i in [1..#Coefficients(n)]]);
    end function;

function nm(n)
    return &+[Abs(x): x in Coefficients(n)]/#Coefficients(n);
    end function;


function scheme(L,t,d: sigma:=3.2,D:=6,eta:=1)
// performs a Base Model circuit with multiplicative depth L-1 and parameters t (plaintext modulus), d (degree of the polynomial defining R), prints the error coefficients in the txt 'file magmaerr' and output true if decryption works correctly
    Z<x> := PolynomialRing(Integers());
    f := x^d+1;
    R<x> := quo<Z|f>;
    K<y> := quo<PolynomialRing(Rationals())|PolynomialRing(Rationals())!f>;

    PE, logdist := genDG(sigma);
    Zt := [-((t-1) div 2)..t div 2]; //(-t/2, t/2]

    Q := genQ(L,t,d,D,eta,sigma);
    Zq := [-((Q-1) div 2)..Q div 2]; //(-Q/2, Q/2]

    P := genP(t,Q);
    PQ := P*Q;
    Zpq := [-((PQ-1) div 2)..PQ div 2]; //(-PQ/2, PQ/2]

    s, a, b := keyGen(R,d,PE,logdist,Q,Zq);
    a2, b2 := kgGHS(R,d,PE,logdist,P,PQ,Zpq,s);

    //generates the independent plaintexts and their encryptions
    m := [R![Random(Zt): j in [1..d]]: i in [1..(2*eta)^(L-1)]];
    c := [encr(R,d,PE,logdist,mi,t,Q,a,b): mi in m];

    //performs a Base Model circuit with no constant multiplications (eta additions, 1 multiplication with relinearization)
    for l in [1..L-1] do
        M := [];
        C := [];
        for i in [0..(#m-1) by (2*eta)] do
            m1 := m[i+1];
            m2 := m[i+eta+1];
            c1 := c[i+1];
            c2 := c[i+eta+1];
            for j in [2..eta] do
                m1 := add(R,m1,m[i+j],t);
                c1 := homAdd(R,c1,c[i+j],Q);
                m2 := add(R,m2,m[i+j+eta],t);
                c2 := homAdd(R,c2,c[i+j+eta],Q);
                end for;
            Append(~M,mult(R,m1,m2,t));
            Append(~C,relinGHS(R,homMult(R,c1,c2,t,Q,P,PQ),Q,P,PQ,a2,b2));
            end for;
        m := M;
        c := C;
        end for;

    // m[1] is the message obtained in clear (working only with plaintexts) and c[1] is its encryption computed from the initial ciphertexts
    nu := noise(R,K,d,m[1],c[1],t,Q,s);
    PrintFile("magmaerr.txt", [RealField()!ci: ci in Coefficients(nu)]);
    return m[1] eq decr(R,c[1],t,Q,s);
    end function;


//scheme(4,3,2^13: D:=8,eta:=8);
