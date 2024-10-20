 //////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
/// LIBRARY CODE (mostly stolen)
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// //more code fro the dafny librayr copied in because copied - dafny.org
  function RemoveKeys<X, Y>(m: map<X, Y>, xs: set<X>): (m': map<X, Y>)
    ensures forall x {:trigger m'[x]} :: x in m && x !in xs ==> x in m' && m'[x] == m[x]
    ensures forall x {:trigger x in m'} :: x in m' ==> x in m && x !in xs
    ensures m'.Keys == m.Keys - xs
    ensures forall x <- m :: (x in xs) != (x in m')
  {
    m - xs
  }



  /* Remove a key-value pair. Returns unmodified map if key is not found. */
  function RemoveKey<X, Y>(m: map<X, Y>, x: X): (m': map<X, Y>)
    ensures m' == RemoveKeys(m, {x})
    ensures |m'.Keys| <= |m.Keys|
    ensures x in m ==> |m'| == |m| - 1
    ensures x !in m ==> |m'| == |m|
    ensures m'.Keys == m.Keys - {x}
    ensures forall x' <- m :: (x == x') != (x' in m')
    ensures forall x' <- m' :: m'[x'] == m[x']
  {
    var m' := map x' | x' in m && x' != x :: m[x'];
    assert m'.Keys == m.Keys - {x};
    m'
  }



datatype Status =
| Success
| Failure(error: string)
{
  predicate IsFailure() { this.Failure? }
  predicate IsSuccess() { this.Success? }

  function PropagateFailure(): Status
    requires IsFailure()
  {
    Failure(this.error)
  }
}


  /* A singleton set has a size of 1. */
  lemma LemmaSingletonSize<T>(x: set<T>, e: T)
    requires x == {e}
    ensures |x| == 1
  {
  }

  /* Elements in a singleton set are equal to each other. */
  lemma LemmaSingletonEquality<T>(x: set<T>, a: T, b: T)
    requires |x| == 1
    requires a in x
    requires b in x
    ensures a == b
  {
    if a != b {
      assert {a} < x;
      LemmaSubsetSize({a}, x);
      assert {:contradiction} |{a}| < |x|;
      assert {:contradiction} |x| > 1;
      assert {:contradiction} false;
    }
  }

  /* A singleton set has at least one element and any two elements are equal. */
  ghost predicate IsSingleton<T>(s: set<T>) {
    && (exists x :: x in s)
    && (forall x, y | x in s && y in s :: x == y)
  }

  predicate GroundSingleton<T>(s: set<T>) : ( r  : bool)
    ensures r ==> (|s| == 1)
   {
    LemmaIsSingleton(s);
    && (exists x :: x in s)
    && (forall x, y | x in s && y in s :: x == y)
  }

  lemma SingletonIsSingleton<T>(s: set<T>)
   ensures IsSingleton(s) <==> GroundSingleton(s)
   {}
  
  /* A set has exactly one element, if and only if, it has at least one element and any two elements are equal. */
  lemma LemmaIsSingleton<T>(s: set<T>)
    ensures |s| == 1 <==> IsSingleton(s)
  {
    if |s| == 1 {
      forall x, y | x in s && y in s ensures x == y {
        LemmaSingletonEquality(s, x, y);
      }
    }
    if IsSingleton(s) {
      var x :| x in s;
      assert s == {x};
      assert |s| == 1;
    }
  }

  /* Non-deterministically extracts an element from a set that contains at least one element. */
  ghost function ExtractFromNonEmptySet<T>(s: set<T>): (x: T)
    requires |s| != 0
    ensures x in s
  {
    var x :| x in s;
    x
  }

  /* Deterministically extracts the unique element from a singleton set. In contrast to 
     `ExtractFromNonEmptySet`, this implementation compiles, as the uniqueness of the element 
     being picked can be proven. */
  function ExtractFromSingleton<T>(s: set<T>): (x: T)
    requires |s| == 1
    ensures s == {x}
  {
    LemmaIsSingleton(s);
    var x :| x in s;
    x
  }

  /* If all elements in set x are in set y, x is a subset of y. */
  lemma LemmaSubset<T>(x: set<T>, y: set<T>)
    requires forall e {:trigger e in y} :: e in x ==> e in y
    ensures x <= y
  {
  }

  /* If x is a subset of y, then the size of x is less than or equal to the
  size of y. */
  lemma LemmaSubsetSize<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
  {
    if x != {} {
      var e :| e in x;
      LemmaSubsetSize(x - {e}, y - {e});
    }
  }

  /* If x is a subset of y and the size of x is equal to the size of y, x is
  equal to y. */
  lemma LemmaSubsetEquality<T>(x: set<T>, y: set<T>)
    requires x <= y
    requires |x| == |y|
    ensures x == y
    decreases x, y
  {
    if x == {} {
    } else {
      var e :| e in x;
      LemmaSubsetEquality(x - {e}, y - {e});
    }
  }

lemma {:only} LemmaSetXsPlusSeperateSingleton<X>(xs : set<X>, x : X, xsPlusX : set<X>) 
  requires x !in xs
  requires xs + {x} == xsPlusX 
  ensures  forall t <- xs :: t in xsPlusX
  ensures  x in xsPlusX
  ensures  xs <= xsPlusX
  ensures  {x} <= xsPlusX
  ensures  forall t <- xsPlusX :: (t in xs) != (t == x)
  ensures  {x} !! xs
  ensures  xsPlusX - {x} == xs
  ensures  xsPlusX - xs  == {x}
{}
  

lemma SubsetOfMapLEQKeys<K,V>(subset : set<K>, left : map<K,V>, right : map<K,V>)
  requires subset <= left.Keys
  requires mapLEQ(left,right)
  ensures  subset <= right.Keys
{
}

predicate mapLEQ<K(==),V(==)>(left : map<K,V>, right : map<K,V>)
{
  (forall k <- left.Keys :: k in right && (left[k] == right[k]))
}


predicate mapGEQ<K(==),V(==)>(left : map<K,V>, right : map<K,V>)
{
  (forall k <- right.Keys :: k in left && (left[k] == right[k]))
}

lemma MapGLEQCCommutative<K,V>(left : map<K,V>, right : map<K,V>)
  ensures  mapLEQ(left, right) ==  mapGEQ(right, left)
{}



lemma BiggerIsBigger<T>(aa : set<T>, bb : set<T>)
     requires aa >= bb
     ensures |aa| >= |bb|
{
  var xs := aa - bb;
  assert |aa| == |bb| + |xs|;
}

lemma FewerIsLess<T>(aa : set<T>, bb : set<T>)
     requires aa <= bb
     ensures |aa| <= |bb|
{
  var xs := bb - aa;
  assert |bb| == |aa| + |xs|;
}



//library version 
lemma IAmTheOne<T>( t : T,  ts : set<T>) 
   requires ((t in ts) && (|ts| == 1))
   ensures ts == {t}
{ 
forall a <- ts, b <- ts
 ensures a == b
 { LemmaSingletonEquality(ts,a,b); }
}

//james version, edited down.
lemma IAmTheOnlyOne<T>( t : T,  ts : set<T>) 
   requires ((t in ts) && (|ts| == 1))
   ensures ts == {t}
{  
  if (ts != {t}) {
    if (ts == {}) { return; }
    var u : T :| u in ts && u != t;
    if (t in ts)  { BiggerIsBigger(ts,{t,u}); }
    return;
   }
}
  
//james' attempt at the full verVMapn with all the working
lemma IAmTheContradictoryOne<T>( t : T,  ts : set<T>) 
   requires ((t in ts) && (|ts| == 1))
     ensures ts == {t}
{  
  if (ts != {t}) 
  {
    if (ts == {}) { assert {:contradiction} |ts| == 0; assert {:contradiction} false; return; }

    var u : T :| u in ts && u != t;

    if (t in ts) { 
        assert t in ts; 
        assert u in ts;
        assert u != t;
        assert ts >= {t,u};
        BiggerIsBigger(ts,{t,u});
        assert {:contradiction} (|ts| >= 2);
        assert {:contradiction} false; return;
      }
     else 
      {
        assert {:contradiction} t !in ts;
        assert {:contradiction} false; return;
      }  
      assert {:contradiction} false; //not reached
    } 
    assert ts == {t};
    }





//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


predicate not(x : bool) { !x }  //becuase sometimes ! is too hard to see!


ghost function gset2seq<T>(X: set<T>) : (S: seq<T>)
  ensures forall x <- X :: x in S
  ensures forall s <- S :: s in X
  ensures |X| == |S|
  ensures forall x <- X :: (multiset(X))[x] == 1
  ensures forall s <- S :: (multiset(S))[s] == 1
  ensures forall i | 0 <= i < |S|, j | 0 <= j < |S| :: (S[i] == S[j]) <==> i == j
  ensures (set s <- S) == X
 {
  var Y := X;
  if (Y == {}) then [] else (
      var y : T :| y in Y;
     [y] + gset2seq( Y - {y} ) )
  } 
//  by method { S := set2seq(X); 
//   assert forall x <- X :: x in S;
//   assert forall s <- S :: s in X;
//   assert |X| == |S|;
//   assert forall x <- X :: (multiset(X))[x] == 1;
//   assert forall s <- S :: (multiset(S))[s] == 1;
//   assert forall i | 0 <= i < |S|, j | 0 <= j < |S| :: (S[i] == S[j]) <==> i == j;
//   assert (set s <- S) == X;
//   assert S == fset2seq(X);
//  }




method set2seq<T>(X: set<T>) returns (S: seq<T>)
  ensures forall x <- X :: x in S
  ensures forall s <- S :: s in X
  ensures |X| == |S|
  ensures forall x <- X :: (multiset(X))[x] == 1
  ensures forall s <- S :: (multiset(S))[s] == 1
  ensures forall i | 0 <= i < |S|, j | 0 <= j < |S| :: (S[i] == S[j]) <==> i == j
  ensures (set s <- S) == X
  // ensures S == gset2seq(X)
  modifies { }
{
  S := []; 
  // var Z := {}; //enshittified the code to do something impossible...
  var Y := X; 
  //  assert S == fset2seq(Z);
  while Y != {}
    decreases Y
    invariant |S| + |Y| == |X|
    invariant forall x <- (X - Y) :: x in S
    invariant forall s <- S :: s in (X - Y)
    invariant forall y <- Y :: y !in S
    invariant forall x <- X :: (multiset(X))[x] == 1
    invariant forall s <- S :: (multiset(S))[s] == 1
    invariant forall i | 0 <= i < |S|, j | 0 <= j < |S| :: (S[i] == S[j]) <==> i == j
   // invariant S == fset2seq(Z)
    {
    var y: T;
    y :| y in Y;
    // assert S == fset2seq(Z);
    // assert S+[y] == fset2seq(Z)+[y];
    // assert S+[y] == fset2seq(Z+{y});
    // S, Z, Y := S+[y], Z+{y}, Y-{y};]
    S, Y := S+[y], Y-{y};
    // assert S == fset2seq(Z);
  }
}

predicate oneWayJesus<T>(X: set<T>, S: seq<T>) //really should be set2seqOK 
{
  && (forall x <- X :: x in S)
  && (forall s <- S :: s in X)
  && (forall x <- X :: (multiset(X))[x] == 1)
  &&( forall s <- S :: (multiset(S))[s] == 1)
  && (|X| == |S|)
  && (forall i | 0 <= i < |S|, j | 0 <= j < |S| :: (S[i] == S[j]) <==> (i == j))

}

lemma ameriChrist<T>(X: set<T>, S: seq<T>)
  requires oneWayJesus(X,S)
  ensures   |X| == |S|
  ensures forall i | 0 <= i < |S|, j | 0 <= j < |S| :: (S[i] == S[j]) <==> (i == j)
{}

lemma oneOfMeFucker<T>(X: set<T>, S: seq<T>, n : nat)
 requires 0 <= n < |S|
 requires oneWayJesus(X,S)
// requires forall i | 0 <= i < |S|, j | 0 <= j < |S| :: (S[i] == S[j]) <==>( i == j)
 ensures forall i | (0 <= i < |S|) && (i != n) :: (S[i] != S[n])
 {
assert oneWayJesus(X,S);
assert forall i | 0 <= i < |S|, j | 0 <= j < |S| :: (S[i] == S[j]) <==> (i == j);
assert forall i | (0 <= i < |S|) && (i != n) :: (S[i] != S[n]);

 }

  
lemma MappingPlusKeysValues<K,V>(am : map<K,V>, bm : map<K,V>, sm : map<K,V>)
  requires sm == am + bm
  ensures  sm.Keys == am.Keys + bm.Keys 
  ensures  sm.Values <= am.Values + bm.Values
{ 
  assert forall k <- am.Keys + bm.Keys :: k in sm.Keys;
  assert am.Keys + bm.Keys <= sm.Keys;
  assert forall k <- sm.Keys :: k in am.Keys || k in bm.Keys;
  assert am.Keys + bm.Keys >= sm.Keys;
  assert am.Keys + bm.Keys == sm.Keys;

  assert forall k <- bm.Values :: k in sm.Values;
  assert forall k <- sm.Values :: k in am.Values || k in bm.Values;

}


/*opaque*/ function MappingPlusOneKeyValue<K(==),V(==)>(m' : map<K,V>, k' : K, v' : V) : (m : map<K,V>)
  requires AllMapEntriesAreUnique(m')
  ensures  AllMapEntriesAreUnique(m)
  requires k' !in m'.Keys 
  requires v' !in m'.Values
  ensures  m == m'[k':=v']
  ensures  m[k'] == v'
  ensures  m.Keys == m'.Keys + {k'}
  ensures  m.Values == m'.Values + {v'}
  ensures  mapLEQ(m',m)
{      
   reveal UniqueMapEntry();

    m'[k':=v']
}


lemma MapLEQKeysValues<K,V>(am : map<K,V>, bm : map<K,V>)
  requires mapLEQ(am,bm)
  ensures  am.Keys <= bm.Keys 
  ensures  am.Values <= bm.Values
{ }



//well it's nice to know I can write this, but the comprehension is much easie r
method set2idMap<T>(X: set<T>) returns (S: map<T,T>)
  ensures forall x <- X :: x in S && S[x] == x
  ensures forall s <- S.Keys :: s in X && S[s] == s
  ensures |X| == |S|
  ensures S.Keys == X
  ensures S.Values == X
  ensures S.Keys == S.Values
  ensures S == map x <- X :: x
{
  S := map[]; var Y := X;
  while Y != {}
    decreases Y
    invariant |S| + |Y| == |X|
    invariant forall x <- (X - Y) :: x in S && S[x] == x
    invariant forall s <- S.Keys :: s in (X - Y) && S[s] == s
  {
    var y: T;
    y :| y in Y;
    S, Y := S[y:=y], Y - {y};
  }
}


//well it's nice to know I can write this, but the comprehension is much easier
method set2constMap<K(==),V(==)>(X : set<K>, v : V) returns (S: map<K,V>)
  ensures forall x <- X :: x in S && S[x] == v
  ensures forall s <- S.Keys :: s in X && S[s] == v
  ensures |X| == |S|
  ensures S.Keys == X
  ensures S.Values <= {v}
  ensures S == map x <- X :: v
{
  S := map[]; var Y := X;
  while Y != {}
    decreases Y
    invariant |S.Keys| + |Y| == |X|
    invariant S.Values <= {v}
    invariant forall x <- (X - Y) :: x in S && S[x] == v
    invariant forall s <- S.Keys :: s in (X - Y) && S[s] == v
  {
    var y: K;
    y :| y in Y;
    S, Y := S[y:=v], Y - {y};
  }
}





function seq2set<T>(q : seq<T>) : set<T> { set x <- q } //Hard to verify??

function seq2set2<T>(q : seq<T>) : set<T> { 
     if |q| == 0 then {} else {q[0]} + seq2set(q[1..]) }




function Extend_A_Map<KV>(m': map<KV,KV>, d : set<KV>) : (m: map<KV,KV>)
//extend m'  with x:=x forall x in d
   requires AllMapEntriesAreUnique(m')
   ensures  AllMapEntriesAreUnique(m)
   requires d !! m'.Keys
   requires d !! m'.Values
   ensures  m == (map x <- d :: x) +  m'
   ensures  m.Keys == m'.Keys + d
   ensures  m.Values == m'.Values + d
  {
   reveal UniqueMapEntry();
   (map x <- d :: x) +  m'
  }

predicate AllMapEntriesAreUnique<K,V(==)>(m : map<K,V>)
{
    reveal UniqueMapEntry();
    forall i <- m.Keys :: UniqueMapEntry(m, i)
}

function invert<K(==),V(==)>(m : map<K,V>) : (n : map<V,K>)
    requires AllMapEntriesAreUnique(m)
    ensures  AllMapEntriesAreUnique(n)
{
      reveal UniqueMapEntry();
      assert forall i <- m.Keys :: UniqueMapEntry(m, i);

      map k <- m.Keys :: m[k] := k
}

lemma InversionLove<K,V>(m : map<K,V>, n : map<V,K>)
  requires AllMapEntriesAreUnique(m)
  requires AllMapEntriesAreUnique(n)
  requires n == invert(m)
  requires m == invert(n)
{
  assert forall k <- m.Keys :: m[k] in n.Keys;
  assert forall k <- m.Keys :: n[m[k]] == k;
  assert forall k <- n.Keys :: n[k] in m.Keys;
  assert forall k <- n.Keys :: m[n[k]] == k;
}

opaque predicate  UniqueMapEntry2<K,V(==)>(m : map<K,V>, k : K) 
 requires k in m
{
  //true
  m[k] !in  (m - {k}).Values  //dodgy UniqueMapEntry //AreWeNotMen
}

opaque predicate   UniqueMapEntry<K,V(==)>(m : map<K,V>, k : K, v : V := m[k]) 
 requires k in m.Keys
{
  //true
  forall i <- m.Keys :: m[i] == v ==> i == k  //dodgy UniqueMapEntry //AreWeNotMen
}


lemma UME1<K,V>(m : map<K,V>, k : K)
 requires k in m
 requires UniqueMapEntry2(m,k)
 ensures  UniqueMapEntry(m,k)
 {
   reveal UniqueMapEntry();
   reveal UniqueMapEntry2();
  assert m[k] !in  (m - {k}).Values;  //dodgy UniqueMapEntry //AreWeNotMen
   var mmk := (m - {k});
   assert m[k] !in (mmk).Values;
   assert forall i <- mmk.Keys :: i != k && m[i] != m[k];
 }

lemma  UME2<K,V>(m : map<K,V>, k : K) 
 requires k in m
 requires UniqueMapEntry(m,k)
 ensures  UniqueMapEntry2(m,k)
  {
   reveal UniqueMapEntry();
   reveal UniqueMapEntry2();
 }


lemma  AValueNeedsAKey<K,V>(v : V, m : map<K,V>)
   requires v in m.Values
   ensures  exists k : K :: k in m.Keys && m[k] == v
  {}

lemma BothSidesNow<K,V>(m : map<K,V>)
  requires AllMapEntriesAreUnique(m)
  ensures  forall i <- m.Keys, k <- m.Keys :: (m[i] != m[k]) ==> (i != k)
  ensures  forall i <- m.Keys, k <- m.Keys :: (m[i] == m[k]) ==> (i == k) 
  ensures  forall i <- m.Keys, k <- m.Keys :: (m[i] != m[k]) <== (i != k)
  ensures  forall i <- m.Keys, k <- m.Keys :: (m[i] == m[k]) <== (i == k) 

{
    reveal UniqueMapEntry();
}

//copied from library?
  ghost predicate {:opaque} Injective<X, Y>(m: map<X, Y>)
  {
    forall x, x' {:trigger m[x], m[x']} :: x != x' && x in m && x' in m ==> m[x] != m[x']
  }

lemma InjectiveIsUnique<K,V>(m : map<K,V>)
  requires Injective(m)
  ensures  AllMapEntriesAreUnique(m)
{  
    reveal Injective();
    reveal UniqueMapEntry();
}

lemma UniqueIsInjective<K,V>(m : map<K,V>)
  requires AllMapEntriesAreUnique(m)
  ensures  Injective(m) 
{
    reveal Injective();
    reveal UniqueMapEntry();
}


/////     /////     /////     /////     /////     /////     /////
    /////     /////     /////     /////     /////     /////     /////
/////     /////     /////     /////     /////     /////     /////
    /////     /////     /////     /////     /////     /////     /////

  
type vmap<K,V> = u : map<K,V> | AllMapEntriesAreUnique(u) 
//intertible map

// method shouldFail() returns (m : vmap<int,int>)
//   //and it does fail
// {
//   m := map[1:=11,2:=11];
// }

function VMapKV<K(==),V(==)>(m' : vmap<K,V>, k : K, v : V) : (m : vmap<K,V>)
//extends m'  with x:=x forall x in d
  //  requires (k !in m'.Keys) && (v !in m'.Values)
  //  requires (forall k' <- m'.Keys :: (k != k') && (v != m'[k']))
   requires canVMapKV(m', k, v)
   ensures  m == m'[k:=v]
   ensures  m.Keys == m'.Keys + {k}
   ensures  m.Values == m'.Values + {v}
  {
      reveal UniqueMapEntry();
      m'[k:=v]
  }

predicate canVMapKV<K(==),V(==)>(m' : vmap<K,V>, k : K, v : V)
  {
     (k !in m'.Keys) && (v !in m'.Values) 
 //  (forall k' <- m'.Keys :: (k != k') && (v != m'[k']))
  }

lemma VMapKVcanVMapKV<K,V>(m' : vmap<K,V>, k : K, v : V)
    requires canVMapKV(m', k, v)
    ensures  VMapKV(m', k, v) == m'[k:=v]
   {}

function mapThruVMap<K,V>(ks : set<K>, m : vmap<K,V>) : set<V>
    requires ks <= m.Keys
  {
      (set k <- ks :: m[k]) 
  }


function mapThruVMapKV<K,V>(ks : set<K>, m' : vmap<K,V>, k : K, v : V) : (m : set<V>)
    requires ks <= m'.Keys+{k}
    requires canVMapKV(m', k, v)    
  {
      (set x <- ks :: m'[k:=v][x]) 
  }

  lemma MapThruVMapKVVMapKV<K,V>(ks : set<K>, m' : vmap<K,V>, k : K, v : V)
    requires ks <= m'.Keys+{k}
    requires canVMapKV(m', k, v)  
    ensures  mapThruVMapKV(ks, m', k, v) == mapThruVMap(ks, VMapKV(m', k, v))
      {
         assert mapThruVMapKV(ks, m', k, v) == (set x <- ks :: m'[k:=v][x]);
         assert mapThruVMapKV(ks, m', k, v) == (set x <- ks :: (VMapKV(m', k, v)[x]));
         assert mapThruVMapKV(ks, m', k, v) == mapThruVMap(ks, (VMapKV(m', k, v)) );
      }



lemma IfImNotTheExtraKeyTheUnderlyingMapIsFine<K,V>(ks : set<K>, m' : vmap<K,V>, k : K, v : V)
    requires ks <= m'.Keys
    requires k !in m'.Keys
    requires canVMapKV(m', k, v)    
    ensures  mapThruVMapKV(ks, m', k, v) == mapThruVMap(ks, m')
    {}


lemma MapThruVMapExtensionality<K,V>(k0 : set<K>, k1 : set<K>, r : set<V>, m : vmap<K,V>)
    requires k0 <= m.Keys
    requires k1 <= m.Keys
  ensures  (mapThruVMap(k0,m) + mapThruVMap(k1,m)) == mapThruVMap(k0+k1, m)
  {}


  lemma MapThruVMapKVExtensionality<K,V>(k0 : set<K>, k1 : set<K>, v0 : set<V>, v1 : set<V>, m : vmap<K,V>,  k : K, v : V)
    requires k0 <= m.Keys
    requires k1 <= m.Keys
    requires v0 <= m.Values
    requires v1 <= m.Values
    requires k0 !! k1
    requires v0 !! v1
    requires mapThruVMap(k0,m) == v0
    requires mapThruVMap(k1,m) == v1

  ensures  (mapThruVMap(k0,m) + mapThruVMap(k1,m)) == mapThruVMap(k0+k1, m) == (v0+v1)
  {}
