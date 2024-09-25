
type Mapping = map<Object,Object>


///shoujld thsi be m.KEys or m.ks...
predicate OrigMapOK(m : Mapping)
{
  && (forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys)
  && (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys)
  && (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner )
  && (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO)
     //  && forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))x
}
predicate ExpandedMapOK(m : Mapping)
{
  && (forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys)
  && (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys)
  && (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner )
  && (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO)

  && (forall x <- m.Keys :: (set oo <- x.AMFO :: m[oo]) == m[x].AMFO) //NEW BIT
     //also needs the first line abofeE= -- x.AMFO in m.Keys

  //  && forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))

  && (forall x <- m.Keys |  x.region.Heap? :: x.extra <= x.AMFO)
  && (forall x <- m.Keys |  x.region.Heap? :: x.extra <= m.Keys)
  && (forall x <- m.Keys, xo <- x.extra :: xo in m.Keys)
  && (forall x <- m.Keys, xo <- x.extra :: m[xo] in m[x].extra)
  && (forall x <- m.Keys :: (set xo <- x.extra :: m[xo]) == m[x].extra)
}

//streamlined MapOK - notably pulled out AMDO & extra to one line each
//
predicate MapOK(m : Mapping)
{
  && (forall k <- m.Keys :: k.AMFO <= m.Keys)
  && (forall k <- m.Keys :: (set oo <- k.AMFO :: m[oo]) == m[k].AMFO)
  && (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
  && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys)
  && (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner )


  //&& (forall x <- m.Keys :: (set oo <- x.AMFO :: m[oo]) == m[x].AMFO) //NEW BIT
     //also needs the first line abofeE= -- x.AMFO in m.Keys

  //  && forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))

/////////  && (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO)

  && (forall x <- m.Keys |  x.region.Heap? :: x.extra <= x.AMFO)
  && (forall x <- m.Keys |  x.region.Heap? :: x.extra <= m.Keys)
  && (forall x <- m.Keys, xo <- x.extra :: xo in m.Keys)
  && (forall x <- m.Keys, xo <- x.extra :: m[xo] in m[x].extra)
  && (forall k <- m.Keys :: (set oo <- k.extra :: m[oo])  == m[k].extra)

}



function MapKV(m : Mapping,   x : Object,  v : Object) : (r : Mapping)
  reads x`fields, x`fieldModes
  requires AllMapEntriesAreUnique(m)
  ensures  AllMapEntriesAreUnique(r)
  requires MapOK(m)
  ensures  MapOK(r)
  requires  //the below should be a predicate (from MapKV)b or MapOK???  or MapWIthKVWouleBeOK?
    && v !in m.Values
    && x !in m.Keys
    && COK(x,m.Keys+{x})
    && x.Ready() && v.Ready()
    && (forall oo <- (x.AMFO - {x}) :: oo in m.Keys)
    && (x.region.Heap? == v.region.Heap?)
    && (x.region.Heap? ==> x.region.owner in x.AMFO)
    && (x.region.Heap? ==> x.region.owner in m.Keys)
    && (forall oo <- x.owners() :: oo in m.Keys &&  m[oo] in v.AMFO)
    && (x.region.Heap? ==> x.region.owner in (x.AMFO - {x}))
    && (x.region.Heap? ==> m[x.region.owner] == v.region.owner)
    && (forall xo <- x.extra :: xo in m.Keys)
    && (forall xo <- x.extra :: m[xo] in v.extra)
       //    && (x.AMFO <= m.Keys) //how the FUCK as the EVER POSSIBLE
    && ((set oo <- x.owners() :: m[oo]) == v.owners()) //NEW BIT  ///note that x can't be in AMFO FUCKER
    && (forall x <- m.Keys :: (set oo <- x.AMFO :: m[oo]) == m[x].AMFO) //NEW BIT


  requires mapThruMappingKV(x.AMFO, m, x, v) == v.AMFO
  requires mapThruMappingKV(x.extra, m, x, v) == v.extra
{
  reveal COK();
  var r := m[x:=v];
  assert COK(x,m.Keys+{x});
  assert MapOK(m);
  assert AllMapEntriesAreUnique(m);
  assert x !in m.Keys;
  assert v !in m.Values;
  assert r.Keys == m.Keys + {x};

  assert m.Keys <= r.Keys;
  assert forall k <- m.Keys :: k in r.Keys;
  assert forall k <- r.Keys :: (k in m.Keys) || (k == x);
  assert forall k <- r.Keys ::
      if (k in m.Keys) then r[k] == m[k] else r[k] == v;


///

  //copied from putINside, which seems WAYY to much duplication
//   assert (forall xx <- m.Keys    :: (set xo <- xx.extra :: m[xo])    ==    m[xx].extra);
//   assert (forall xx <- m.Keys    :: (set xo <- xx.extra :: r[xo]) == r[xx].extra);
//   assert (forall xx <- r.Keys :: (set xo <- xx.extra :: r[xo]) == r[xx].extra);
//
//
//
//   assert (forall xo <- x.extra :: xo in r.Keys);
//   assert (forall xo <- x.extra :: r[xo] in r[x].extra);
//   assert (forall xo <- x.extra :: xo in r.Keys);
//   assert (forall xo <- x.extra :: r[xo] in r[x].extra);
//
//   assert (forall xx <- {x}, xo <- xx.extra :: xo in r.Keys);
//   assert (forall xx <- {x}, xo <- xx.extra :: r[xo] in r[xx].extra);
//   assert (forall xx <- {x}, xo <- xx.extra :: r[xo] in r[xx].extra);
//
//   assert (forall xx <- m.Keys :: (set xo <- xx.extra :: m[xo]) == m[xx].extra);
//   assert (forall xx <- r.Keys :: (set xo <- xx.extra :: r[xo]) == r[xx].extra); //EXTRA BIT :-)

// was going to work on this bit...
//   assert (forall xx <- m.Keys :: (set oo <- xx.AMFO ::  m[oo]) == m[xx].AMFO); //NEW BIT
//   assert (forall xx <- m.Keys :: (set oo <- xx.AMFO ::  r[oo]) == r[xx].AMFO); //NEW BIT
//   assert (forall xx <- {x}    :: (set oo <- xx.AMFO ::  r[oo]) == r[xx].AMFO); //NEW BIT
//   assert r.Keys == m.Keys + {x};
//   assert (forall xx <- r.Keys :: (set oo <- xx.AMFO ::  r[oo]) == r[xx].AMFO); //NEW BIT



  //   assert (forall x <- r.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO) by {
  //             assert (forall oo <- x.AMFO :: r[oo] in r[x].AMFO);
  //             assert (forall x <- m.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO);
  //             assert r.Keys == m.Keys + {x};
  //             assert (forall x <- r.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO);
  //             }
  //   assert (forall x <- r.Keys | x.region.Heap? :: r[x.region.owner] == r[x].region.owner) by {
  //             assert (forall x <- m.Keys | x.region.Heap? :: m[x.region.owner] == r[x].region.owner);
  //             assert (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == r[x].region.owner);
  //             assert r.Keys == m.Keys + {x};
  //             assert (forall x <- r.Keys | x.region.Heap? :: r[x.region.owner] == r[x].region.owner);
  //             }

  assert (forall x <- r.Keys :: x.region.Heap? == r[x].region.Heap?) by {
    assert (forall x <- m.Keys :: x.region.Heap? == r[x].region.Heap?);
    assert r.Keys == m.Keys + {x};
    assert (forall x <- r.Keys :: x.region.Heap? == r[x].region.Heap?);
  }

  assert (&& (forall x <- m.Keys, xo <- x.extra :: xo in m.Keys)
          && (forall x <- r.Keys, xo <- x.extra :: r[xo] in r[x].extra)) by {
    assert (forall x <- m.Keys, xo <- x.extra :: m[xo] in m[x].extra);
    assert forall k <- r.Keys ::
        if (k in m.Keys) then r[k] == m[k] else r[k] == v;
    assert (forall x <- m.Keys, xo <- x.extra :: r[xo] in m[x].extra);
    assert r.Keys == m.Keys + {x};
    assert x in r.Keys;
    assert (forall xo <- x.extra :: m[xo] in v.extra);
    assert (forall x <- r.Keys, xo <- x.extra :: r[xo] in r[x].extra);
  }


  assert (forall x <- r.Keys :: (set oo <- x.extra :: r[oo]) == r[x].extra)
  by {
    assert MapOK(m);
    assert (forall x <- m.Keys :: (set oo <- x.extra :: m[oo]) == m[x].extra);
    assert (forall k <- r.Keys ::  if (k in m.Keys) then r[k] == m[k] else r[k] == v);
    assert (forall x <- m.Keys :: (set oo <- x.extra :: r[oo]) == r[x].extra);
//    assert (set oo <- (x.extra) :: m[oo]) == v.extra;
//    assert (set oo <- (x.extra) :: r[oo]) == v.extra;

    assert r[x] == v;
    assert r.Keys == m.Keys + {x};
    assert (forall x <- r.Keys :: (set oo <- x.extra :: r[oo]) == r[x].extra);
  }

  assert FUCKA: (forall x <- r.Keys :: (set oo <- x.extra :: r[oo]) == r[x].extra);



  assert (forall x <- r.Keys |  x.region.Heap? :: r[x.region.owner] == r[x].region.owner )
  by {
    assert MapOK(m);
    assert (forall x <- m.Keys |  x.region.Heap? ::  m[x.region.owner] == m[x].region.owner );
    assert forall k <- r.Keys ::
        if (k in m.Keys) then r[k] == m[k] else r[k] == v;
    assert (forall x <- m.Keys |  x.region.Heap? ::  r[x.region.owner] == r[x].region.owner );
    assert x.region.Heap? ==>  (r[x.region.owner] == r[x].region.owner);
    assert (forall x <- r.Keys |  x.region.Heap? :: r[x.region.owner] == r[x].region.owner );
  }

  assert (forall x <- r.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO)
  by {
    assert MapOK(m);
    assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);
    assert forall k <- r.Keys ::
        if (k in m.Keys) then r[k] == m[k] else r[k] == v;
    assert (forall x <- m.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO);
    assert (forall oo <- x.AMFO - {x} :: r[oo] in v.AMFO);
    assert r[x] == v;
    assert (x in x.AMFO) && (v in v.AMFO) && (r[x] in r[x].AMFO);
    assert (forall x <- r.Keys, oo <- x.AMFO :: r[oo] in r[x].AMFO);
  }


  assert (forall x <- r.Keys :: (set oo <- x.AMFO :: r[oo]) == r[x].AMFO)
  by {
    assert MapOK(m);
    assert (forall x <- m.Keys :: (set oo <- x.AMFO :: m[oo]) == m[x].AMFO);
    assert (forall k <- r.Keys ::  if (k in m.Keys) then r[k] == m[k] else r[k] == v);
    assert (forall x <- m.Keys :: (set oo <- x.AMFO :: r[oo]) == r[x].AMFO);
//    assert (set oo <- x.AMFO :: r[oo]) == r[x].AMFO;
assert mapThruMappingKV(x.AMFO, m, x, v) == v.AMFO;
     assert ((set oo <- x.AMFO :: r[oo]) == v.AMFO);
    assert (forall k <- {x} :: (set oo <- k.AMFO :: r[oo]) == v.AMFO);
    assert r[x] == v;
    assert r.Keys == m.Keys + {x};
    assert ( x in x.AMFO) && (v in v.AMFO) && (r[x] in r[x].AMFO);
    assert (set oo <- x.AMFO :: r[oo]) == v.AMFO;
    assert (forall k <- m.Keys+{x} :: (set oo <- k.AMFO :: r[oo]) == r[k].AMFO);

    assert (forall x <- r.Keys :: (set oo <- x.AMFO :: r[oo]) == r[x].AMFO);
  }




  assert AllMapEntriesAreUnique(r) by {
    reveal UniqueMapEntry();
    assert AllMapEntriesAreUnique(m);
    assert forall i <- m.Keys :: UniqueMapEntry(m, i);
    assert x !in m.Keys;
    assert v !in m.Values;
    assert forall i <- (m.Keys+{x}) :: UniqueMapEntry(r, i);
    assert (m.Keys+{x}) == r.Keys;
    assert forall i <- (r.Keys) :: UniqueMapEntry(r, i);
    assert AllMapEntriesAreUnique(r);
  }
  assert MapOK(r) by {
    reveal FUCKA;
    assert (forall x <- r.Keys :: (set oo <- x.extra :: r[oo]) == r[x].extra);
  }
  r
}//MapKV

lemma MapKVOK(m : Mapping,   x : Object,  v : Object, r : Mapping)
  requires AllMapEntriesAreUnique(m)
  ensures  AllMapEntriesAreUnique(r)
  requires MapOK(m)
  ensures  MapOK(r)
  requires  //the below should be a predicate (from MapKV)
    && x !in m.Keys
    && v !in m.Values
       //&& COK(x,m.Keys)
    && x.Ready() && v.Ready()
    && (forall oo <- (x.AMFO - {x}) :: oo in m.Keys)
    && (x.region.Heap? == v.region.Heap?)
    && (x.region.Heap? ==> x.region.owner in x.AMFO)
    && (x.region.Heap? ==> x.region.owner in m.Keys)
    && (forall oo <- (x.AMFO - {x}) :: oo in m.Keys &&  m[oo] in v.AMFO)
    && (x.region.Heap? ==> x.region.owner in (x.AMFO - {x}))
    && (x.region.Heap? ==> m[x.region.owner] == v.region.owner)
    && (x.region.Heap? ==> x.extra <= x.AMFO)
    && (forall xo <- x.extra :: xo in m.Keys)
    && (forall xo <- x.extra :: m[xo] in v.extra)
    && (x.AMFO <= m.Keys)    /// implies x in m.Keys... which is WRONG
    && ((set oo <- x.AMFO :: m[oo]) == v.AMFO) //NEW BIT
    && (forall x <- m.Keys :: (set oo <- x.AMFO :: m[oo]) == m[x].AMFO) //NEW BIT

  requires r == MapKV(m,x,v)

  ensures r.Keys == m.Keys + {x}
  ensures forall i <- m.Keys :: i in r.Keys
  ensures forall i <- m.Keys :: m[i] == r[i]
  ensures forall i <- r.Keys :: if (i == x) then (r[i] == v) else (r[i] == m[i])
{
  reveal COK();
  var r := m[x:=v];
  //  assert COK(x,m.Keys);
  assert MapOK(m);
  assert AllMapEntriesAreUnique(m);
  assert x !in m.Keys;
  assert v !in m.Values;
  assert r.Keys == m.Keys + {x};

  assert m.Keys <= r.Keys;
  assert forall k <- m.Keys :: k in r.Keys;
  assert forall k <- r.Keys :: (k in m.Keys) || (k == x);
  assert forall k <- r.Keys ::
      if (k in m.Keys) then r[k] == m[k] else r[k] == v;

}




datatype Map = Map(
  m : Mapping,  //m : Mapping
  ks : set<Object>, //ks - set, keys of the mapping   (must be m.Keys, subset of oHeap)
  vs : set<Object>, //vs - set, values or the mapping (must be m.Values, subset of oHeap + ns)
  o : Object,  //o - Owner within which the clone is being performaed, in oHeap
  //    p : Object,  // Owner of the new (target) clone.  needs to be inside the source object's movement
  oHeap : set<Object>,  //oHeap - original (sub)heap contianing the object being cloned and all owners and parts
  ns : set<Object>) //ns - new objects  (must be !! oHeap,   vs <= oHeap + ns
{
  // general rule: where possible, work with ks and vs rther than m.Keys & m.Values...
  // that's the point of setting this up, right?


  predicate fromold(prev : Map)
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    reads prev.oHeap`fields, prev.oHeap`fieldModes
    reads prev.ns`fields, prev.ns`fieldModes
  {
    reveal calid(), calidObjects(), calidOK(), calidMap(), calidSheep();
    //      old(from(prev))

    && calid()         //should these be requirements?
       // && old(prev.calid())
    && mapGEQ(m, prev.m)
    && ks    >= prev.ks
    && vs    >= prev.vs
    && o     == prev.o
    && oHeap == prev.oHeap
    && ns    >= prev.ns
  }



  predicate from(prev : Map)
    // should this be unique or not?
    // m.from(prev) assuming prev.MapOK, then I',m Map(OK) and a a "strict but improper extension"
    // strict - thijngs like oHeap can't change
    // improper - could be exactly the same as prev
    //
    // if most things are OK,  given xown, xm := foo(own, m);
    // then we should have xm.from(m);  I THINK??
    //
/// what's really annoy6ing is: should I keep track of the first from?
    // cos usually that's what I need to prove.
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    reads prev.oHeap`fields, prev.oHeap`fieldModes
    reads prev.ns`fields, prev.ns`fieldModes
    //     requires calid()
    //     requires prev.calid()
  {
    reveal calid(), calidObjects(), calidOK(), calidMap(), calidSheep();
    && calid()         //should these be requirements?
       //       && prev.calid()   //currently YES because the underlyign thing will require calid and reutnr calid
    && mapGEQ(m, prev.m)
    && ks    >= prev.ks
    && vs    >= prev.vs
    && o     == prev.o
    && oHeap == prev.oHeap
    && ns    >= prev.ns
  }


  static lemma fromityH(a : Object, context : set<Object>, prev : Map, next: Map)
    requires prev.calid()
    requires next.calid()
    requires next.from(prev)

    requires context <= prev.oHeap
    requires COK(a,context)

    ensures context <= next.oHeap
    ensures COK(a,next.oHeap)
  {
    COKWiderContext2(a,context,next.oHeap);
  }

  twostate predicate allUnchangedExcept(except : set<Object> := {})
    reads vs, ks, o, oHeap
  {
    &&  unchanged(vs - except)
    &&  unchanged(ks - except)
    &&  unchanged({o} - except)
    &&  unchanged(oHeap - except)
  }




  opaque function at(k : Object) : (v : Object)
    //return value corresponding to key k
    //k must be in the map
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calid()
    requires k in ks
    //requires reveal calid(); reveal calidObjects();  ks == m.Keys
    //requires k in m.Keys
    ensures  k in ks
    ensures  k in m.Keys //to guard the next one
    ensures  v == m[k]
    // ensures  k == atV(v)
  {  reveal calid(); reveal calidObjects();
    assert k in m.Keys;
    m[k] }




  method superTRUMP(k : Object, v : Object)
    requires COK(k, {k})
    requires CallOK({}, {k})
    requires CallOK({k})
    requires ExtraIsExtra({},{k})
    requires AllTheseOwnersAreFlatOK(k.AMFO)
    requires AllTheseOwnersAreFlatOK({}, k.AMFO + {})
  {
    var jd := new Object.cake( map[], k, {k}, "hello");
    assert jd !in oHeap;
    Vance(jd);
  }

  method Vance(v : Object)
    requires v !in oHeap
  {}



  lemma habeusKeyus(k : Object, v : Object)
    requires calid()
    //requires v in vs
    requires (k in ks) ==> (m[k] == v)

    // requires  k in ks
    // requires  k in m.Keys //to guard the next one

    // ensures  v  in ns ==> k  in ks
    // ensures  k !in ks ==> v !in ns
    ensures  (v !in ns) && (v in vs) ==> v in oHeap

  {
    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    reveal calidMap();
    assert calidMap();
    assert MapOK(m);
    assert ns <= vs;

    if (v in ns) {
      assert v in vs;
      assert gotV(v);
      assert AllMapEntriesAreUnique(m);
      AValueNeedsAKey(v, m);
    } else {
      assert  v !in ns;

    }
  }

  static lemma roundTrip1(k : Object, v : Object, m : Map)
    requires m.calid()
    requires m.got(k)
    requires m.at(k) == v
    ensures  m.atV(v) == k
  {
    reveal m.calid();
    assert m.calid();
    reveal m.calidObjects();
    assert m.calidObjects();
    reveal m.calidMap();
    assert m.calidMap();
    assert MapOK(m.m);
    assert AllMapEntriesAreUnique(m.m);

    reveal atV();
    reveal at();
    reveal UniqueMapEntry();

    assert m.at(k)  == v;  //why is this needed?
    assert m.m[k]   == v;
    assert forall i <- m.m.Keys :: UniqueMapEntry(m.m, i);
    assert k in m.m.Keys;
    assert UniqueMapEntry(m.m, k);
    assert m.atV(v) == k;
  }

  static lemma roundTrip2(k : Object, v : Object, m : Map)
    requires m.calid()
    requires m.gotV(v)
    requires m.atV(v) == k
    ensures m.at(k) == v
  {
    reveal m.calid();
    assert m.calid();
    reveal m.calidObjects();
    assert m.calidObjects();
    reveal m.calidMap();
    assert m.calidMap();
    assert MapOK(m.m);
    assert AllMapEntriesAreUnique(m.m);
  }

  opaque ghost function atV(v : Object) : (k : Object)
    //return key corresponding to value v
    //v must be in the map
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calid()
    requires v in vs
    //requires reveal calid(); reveal calidObjects();  ks == m.Keys
    //requires k in m.Keys
    ensures  k in ks
    ensures  k in m.Keys //to guard the next one
    ensures  v == m[k]
  {  reveal calid(); reveal calidObjects(); reveal calidMap();
    assert calid(); assert calidObjects(); assert calidMap();
    assert v in m.Values;
    AValueNeedsAKey(v, m);
    assert AllMapEntriesAreUnique(m);
    var k' :| k' in m.Keys && m[k'] == v;
    k' }

  opaque predicate  {:onleee} got(k : Object) : (g : bool)
    //is k in the map?
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calid()
    ensures  g == (k in ks)
    ensures  g == (k in m.Keys)  //DO I WANT THIS?
  {
    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    k in ks
  }


  opaque predicate gotV(v : Object) : (g : bool)
    //is v a value in the map?
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calid()
    ensures  g == (v in vs)
    ensures  g == (v in m.Values)  //DO I WANT THIS?
  {
    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    v in vs
  }


  opaque function {:isolate_assertions} putInside(k : Object, v : Object) : (r : Map)
    //put k -> v into map, k inside o
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes,  v`fields, v`fieldModes
    requires calid()
    requires k  in oHeap
    requires k !in ks
    requires k !in m.Keys
    requires v !in oHeap
    requires v !in ns
    requires v !in vs
    requires v !in m.Values
    requires COK(k, oHeap)
    requires COK(v, oHeap+ns+{v})
    requires ks <= oHeap
    requires k.owners() <= ks  //need to update - all my owners EXCEPT ME!
    requires k.owners() <= m.Keys
    requires v.owners() <= oHeap+ns //need to hae proceessed all owners first
    // requires v in (oHeap + ns) // should be a SEPERATIJG COJUNCTION (Below)
    // requires ((v in oHeap) != (v in ns))  //NOPE for now put it in ns
    requires k.region.Heap? == v.region.Heap?
    requires k.region.Heap? ==> v.region.Heap? && (k.region.owner in m.Keys) && (m[k.region.owner] == v.region.owner)
    requires forall ko <- k.owners() :: ko in m.Keys
    requires forall ko <- k.owners() :: m[ko] in v.AMFO
    //    requires mapThruMap(k.owners(), this) == (v.AMFO - {v})
    requires ((set oo <- k.owners() :: m[oo]) == v.owners())
    requires mapThruMapKV(k.AMFO, this, k, v) == v.AMFO

    requires forall kx <- k.extra :: kx in m.Keys
    requires forall kx <- k.extra :: m[kx] in v.extra
    //      requires k.region.Heap? ==> (k.region.owner in m && m[k.region.owner] == v.region.owner)
    //      requires reveal calid(); (calid() && k.region.Heap?) ==> (got(k.region.owner) && (at(k.region.owner) == v.region.owner))
    //requires fresh(v)
    requires inside(k, o)
    requires v.fieldModes == k.fieldModes

    ensures  r == Map(m[k:=v], ks+{k}, vs+{v}, o, oHeap, ns+{v})
    ensures  r.m.Keys == r.ks
    ensures  r.m.Values == r.vs
    ensures  v in r.ns
    ensures  k in r.ks && r.m[k] == v
    ensures  COK(v, r.oHeap+r.ns)
    ensures  k in r.m.Keys
    ensures  v in r.m.Values
    ensures  r.m == m[k:=v]
    ensures  mapLEQ(m, r.m)
    ensures  r.calid()
    ensures  r.from(this)
    ensures  AllMapEntriesAreUnique(this.m)
    ensures  r.m == MappingPlusOneKeyValue(this.m,k,v)
  {

    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    reveal calidOK();
    assert calidOK();

    assert ks == m.Keys;
    assert calidMap();
    reveal calidMap();
    assert calidSheep();
    reveal calidSheep();

    assert MapOK(m);
    assert CallOK(oHeap);
    assert COK(k, oHeap);
    assert COK(v, oHeap+ns+{v});

    reveal COK();

    assert AllMapEntriesAreUnique(m);



    reveal calid(); assert calid();
    var rv := Map(m[k:=v], ks+{k}, vs+{v}, o, oHeap, ns+{v});

    reveal calidMap(); assert calidMap(); assert MapOK(m);

    assert MapKV(m,k,v) == m[k:=v] by { reveal calidMap(); assert calidMap(); assert MapOK(m);}
    assert rv.m == MapKV(m,k,v);

    assert oXn: oHeap !! ns by { assert calid(); assert calidObjects(); reveal calidObjects();}

    assert COK(v, rv.oHeap+rv.ns) by {
      assert COK(v, oHeap+ns+{v});  // from reqs
      assert rv.oHeap      == oHeap;
      assert rv.ns         == ns+{v};
      assert rv.oHeap+rv.ns == oHeap+ns+{v};
      assert COK(v, rv.oHeap+rv.ns);
    }

    assert rv.calidObjects() by {
      reveal rv.calidObjects();

      assert rv.ks == rv.m.Keys;
      assert rv.vs == rv.m.Values;
      assert rv.o in rv.oHeap;
      assert rv.ks <= rv.oHeap;
      assert rv.ns !! rv.oHeap by {
        assert ns !! oHeap by { reveal oXn; }
        assert v !in oHeap;
        assert {v} !! oHeap;
        assert (ns + {v}) !! oHeap;
        assert rv.oHeap == oHeap;
        assert (ns + {v}) !! rv.oHeap;
        assert rv.ns == ns+{v};
        assert rv.ns !! rv.oHeap;
      }
      assert rv.vs <= rv.ns + oHeap;

      assert rv.calidObjects();
    }

    assert v !in vs; // from reqs
    assert vs == m.Values by {
      assert calid();
      reveal calid();
      assert calidObjects();
      reveal calidObjects();
      assert vs == m.Values;
    }
    assert v !in m.Values;

    assert rv.calidOK() by {
      reveal rv.calidOK();
      reveal rv.calidObjects();
      assert COK(rv.o, rv.oHeap);
      assert CallOK(rv.oHeap);
      CallOKfromCOK(k, oHeap);
      assert CallOK(ks, oHeap);
      CallOKtoSubset(ks, oHeap);
      CallOKWiderFocus(ks, {k}, oHeap);
      assert CallOK(rv.ks, rv.oHeap);
      assert oHeap+ns+{v} == rv.oHeap+rv.ns;
      assert COK(v, rv.oHeap+rv.ns);
      // CallOKWiderContext({v}, rv.oHeap, rv.ns);    //unneeded?
      // CallOKtoSubset(rv.vs, rv.oHeap+rv.ns);       //unneeded?
      assert rv.vs <= rv.ns + oHeap;
      assert CallOK(vs, oHeap+ns);
      CallOKWiderContext(vs, oHeap+ns, {v});
      assert COK(v,oHeap+ns+{v}); //reqs
      CallOKfromCOK(v, oHeap+ns+{v});   //could subsume within COK?> (or not0)
      CallOKWiderFocus(vs, {v}, oHeap+ns+{v});  //version just adding one?
      assert vs+{v} == rv.vs;
      assert CallOK(rv.vs, rv.oHeap+rv.ns);
      assert ns+{v} == rv.ns;
      CallOKWiderContext(ns,oHeap+ns,{v});  //is it worth cobinging these also
      CallOKWiderFocus(ns,{v},oHeap+ns+{v});
      assert CallOK(rv.ns, rv.oHeap+rv.ns);
      reveal rv.calidOK(); assert rv.calidOK();
    }


    // reveal rv.calidMap();
    // assert rv.calidMap() by {
    reveal rv.calidMap();
    assert MapOK(rv.m) by {
      assert MapOK(m);
      assert COK(k, oHeap);
      reveal COK();
      assert rv.ks == ks + {k};
      assert rv.m.Keys == m.Keys + {k};

      reveal rv.calidObjects();
      assert rv.calidObjects();
      reveal calidObjects();
      assert calidObjects();
      reveal calidMap();
      assert calidMap();

      assert rv.m.Keys == rv.ks;
      assert k.owners() <= ks;

      assert forall x <- m.Keys :: x.AMFO <= ks by {
        assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys;
      }
      assert k.owners() <= ks;
      //  assert forall x <- m.Keys+{k} :: x.owner() <= ks;
      assert forall x <- m.Keys+{k} :: x.AMFO <= ks+{k};
      assert (ks+{k}) == m.Keys+{k} == rv.ks == rv.m.Keys;
      assert forall x <- rv.m.Keys :: x.AMFO <= rv.m.Keys;
      assert forall x <- rv.m.Keys, oo <- x.AMFO :: oo in rv.m.Keys;


      assert (forall x <- rv.m.Keys :: x.region.Heap? == rv.m[x].region.Heap?);
      assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO);
      assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in rv.m.Keys);
      assert (forall x <- rv.m.Keys |  x.region.Heap? :: rv.m[x.region.owner] == rv.m[x].region.owner );

      // //BEGIN DUNNO ABOUT THIS
      //       assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);
      //       assert (forall x <- m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
      //       assert rv.m[k] == v;
      //       assert ks == m.Keys;
      //       assert (k.owners() <= ks);
      //       assert (k.AMFO - {k}) <= ks;
      //       assert (forall oo <- (k.AMFO - {k}):: oo in m.Keys);
      //       assert (forall oo <- (k.AMFO - {k}):: m[oo] in v.AMFO);
      //       assert (forall oo <- (k.AMFO - {k}):: rv.m[oo] in rv.m[k].AMFO);
      //
      //       assert (forall x <- m.Keys, xo <- x.extra :: xo in m.Keys);
      //       assert (forall x <- m.Keys, xo <- x.extra :: m[xo] in m[x].extra);
      //       assert (forall x <- m.Keys, xo <- x.extra :: xo in rv.m.Keys);
      //       assert (forall x <- m.Keys, xo <- x.extra :: rv.m[xo] in rv.m[x].extra);
      //END DUNNO ABOUT THIS

      assert rv.m.Keys == m.Keys + {k};
      assert rv.m == MapKV(m,k,v);

      assert (forall x <- m.Keys    :: (set xo <- x.extra :: m[xo])    ==    m[x].extra);
      assert (forall x <- m.Keys    :: (set xo <- x.extra :: rv.m[xo]) == rv.m[x].extra);
      assert (forall x <- rv.m.Keys :: (set xo <- x.extra :: rv.m[xo]) == rv.m[x].extra);



      assert (forall xo <- k.extra :: xo in rv.m.Keys);
      assert (forall xo <- k.extra :: rv.m[xo] in rv.m[k].extra);
      assert (forall xo <- k.extra :: xo in rv.m.Keys);
      assert (forall xo <- k.extra :: rv.m[xo] in rv.m[k].extra);

      assert (forall x <- {k}, xo <- x.extra :: xo in rv.m.Keys);
      assert (forall x <- {k}, xo <- x.extra :: rv.m[xo] in rv.m[x].extra);

      assert mapThruMapKV(k.AMFO, this, k, v) == v.AMFO;

      assert (forall x <- m.Keys :: (set oo <- x.AMFO :: m[oo]) == m[x].AMFO); //NEW BIT
      assert (forall x <- rv.m.Keys :: (set oo <- x.AMFO :: rv.m[oo]) == rv.m[x].AMFO);

      assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
      assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.extra <= x.AMFO);
      assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.extra <= rv.m.Keys);
      assert (forall x <- rv.m.Keys, xo <- x.extra :: xo in rv.m.Keys);
      //      assert (forall x <- rv.m.Keys, xo <- x.extra :: rv.m[xo] in rv.m[x].extra);

      //       assert mapThruMap(k.owners(), this) == (v.AMFO - {v});
      //       assert mapThruMap(k.owners(), this) == (v.owners());
      //  //   assert mapThruMap(k.AMFO, this) == (v.AMFO);//doesn't work cos k not in this.m.Keys
      //       assert ((set oo <- (k.AMFO - {k}) :: m[oo]) == v.AMFO - {v});
      //       assert ((set oo <- (k.owners()) :: m[oo]) == v.owners());
      // //    assert (forall x <- {k}     :: (set oo <- x.owners() :: m[oo]) == m[x].owners());  //dpoesn't work cos K NOT IN M yet
      //       assert (forall x <- {k}     :: (set oo <- x.owners() :: m[oo]) == v.owners());  //does work tho' K NOT IN M yet
      //
      //       assert (forall x <- m.Keys     :: (set oo <- x.AMFO ::       m[oo]) == m[x].AMFO);
      //       assert (forall x <- m.Keys     :: mapThruMap(x.AMFO, this)          == m[x].AMFO);
      //
      //       assert (forall x <- m.Keys + {k}
      //               :: (set oo <- x.AMFO :: if (oo == k) then (v) else (m[oo]))
      //                                    == if (x  == k) then (v.AMFO) else (m[x].AMFO));
      //
      // //    assert (forall x <- m.Keys + {k} :: mapThuMap(x.AMFO, this) == if x in m.Keys then (m[x].AMFO) else (v.AMFO)); //again k not in this & mapThru needs calid
      //
      //       assert k !in m.Keys;
      // //      var n := m[k:=v];
      // assert k.owners() <= m.Keys;
      //       var n := MapKV(m,k,v);
      //       MapKVOK(m,k,v,n);
      //       assert n.Keys == m.Keys + {k};
      //       assert (forall x <- m.Keys :: x in n.Keys);
      //       assert (forall x <- (m.Keys * n.Keys) :: (m[x] == n[x]));
      //
      //       assert (forall x <- n.Keys     :: (set oo <- x.AMFO ::       n[oo]) == n[x].AMFO);
      //
      // //    assert (forall x <- m.Keys+{k} :: (set oo <- x.AMFO :: m[k:=v][oo]) == m[k:=v][x].AMFO);
      // //    assert (forall x <- rv.m.Keys  :: mapThruMap(x.AMFO, rv)            == rv.m[x].AMFO); //OOPS mapThruMap needs calid...
      //       assert (forall x <- rv.m.Keys  :: (set oo <- x.AMFO ::    rv.m[oo]) == rv.m[x].AMFO);


    }  //MapOK



    reveal rv.calidObjects();
    assert ks == m.Keys;
    assert rv.ks == rv.m.Keys;

    assert (inside(k,rv.o)) ==> (rv.m[k] in ns);
    assert rv.m[k] == v;
    assert v in ns;
    assert inside(k,rv.o);

    assert (forall x <- ks  :: (not(inside(x,o)) ==> (m[x] == x)));
    assert (forall x <- ks  :: (not(inside(x,o)) ==> (rv.m[x] == x)));
    assert (forall x <- {k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
    assert (forall x <- ks+{k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
    assert rv.ks == ks + {k};
    assert rv.ks == rv.m.Keys;
    assert (forall x <- rv.ks  :: (not(inside(x,o)) ==> (rv.m[x] == x)));

    assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
    assert (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO);

    reveal rv.calidMap();

    reveal UniqueMapEntry();

    assert AllMapEntriesAreUnique(m);
    assert forall i <- m.Keys :: UniqueMapEntry(m, i);
    assert k !in ks;
    assert v !in vs;
    assert forall i <- m.Keys :: i != k;
    assert forall i <- m.Keys :: m[i] != v;
    assert forall i <- m.Keys+{k} :: (rv.m[i] == v ) ==> (k == i);
    assert forall i <- rv.m.Keys :: UniqueMapEntry(rv.m, i);

    assert
      && AllMapEntriesAreUnique(rv.m)
      && MapOK(rv.m) // potentiall should expand this out?
      && (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)))
      && (forall x <- rv.ks, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO)
      ;

    assert rv.calidMap();

    reveal rv.calidSheep();
    reveal rv.calidObjects();
    assert ks == m.Keys;
    assert rv.ks == rv.m.Keys;
    assert inside(k, o);
    reveal calidMap();
    assert calidMap();
    reveal calidSheep();


    assert forall x <- ks :: AreWeNotMen(x, this);
    assert rv.ks == rv.m.Keys == (ks+{k});

    assert forall x <- ks :: x.fieldModes == m[x].fieldModes;
    assert k.fieldModes == v.fieldModes;
    assert forall x <- rv.ks :: x.fieldModes == rv.m[x].fieldModes;

    assert calidSheep();
    reveal rv.calidSheep();
    //reveal UniqueMapEntry();

    assert ks == m.Keys;

    reveal AreWeNotMen();
    reveal UniqueMapEntry();
    assert forall x <- ks  :: AreWeNotMen(x, this);
    assert forall x <- {k} :: AreWeNotMen(x, rv);
    assert forall x <- rv.m.Keys :: AreWeNotMen(x, rv);

    assert rv.calidSheep();
    reveal rv.calid(); assert rv.calid();

    rv
  } //END putInside
  //
  //
  // lemma OutsidfeValuesAreUniqueDuh()
  //   requires calid()
  //   ensures  forall k <- ks ::
  // {
  //   reveal calid();
  //   )
  //

  opaque function {:isolate_assertions} putOutside(k : Object) : (r : Map)
    //put k -> k into map, k oustide o
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calid()
    requires k !in ks
    requires k !in vs
    requires k !in m.Keys
    requires k !in m.Values
    requires k in oHeap
    requires COK(k, oHeap)
    requires k.owners() <= ks
    requires not(inside(k, o))

    requires
      && k !in m.Keys && k !in m.Values
      && COK(k,oHeap)
      && k.Ready()
      && k.AllOwnersAreWithinThisHeap(ks)
      && (forall oo <- k.AMFO - {k}:: oo in m.Keys)
         //  && (k.region.Heap? ==> m[k].region.Heap?)  WHATR THE FUCK k at in the map!
      && (k.region.Heap? ==> k.region.owner in k.AMFO)
      && (k.region.Heap? ==> k.region.owner in m.Keys)
         // && (k.region.Heap? ==> m[k.region.owner] == m[k].region.owner )
         //  && (forall oo <- k.AMFO :: m[oo] in m[k].AMFO)
      && (k.region.Heap? ==> k.extra <= k.AMFO)
      && (forall xo <- k.extra :: xo in m.Keys)
    // && (forall xo <- k.extra :: m[xo] in m[k].extra)




    requires forall kx <- k.extra :: kx in m.Keys
    requires forall kx <- k.extra :: m[kx] == kx

    ensures r == Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns)
    ensures k in r.ks && r.m[k] == k
    ensures k in r.m.Keys
    ensures k in r.m.Values
    ensures MapOK(r.m)
    ensures weirdo() && (r.m == MapKV(this.m,k,k))
    ensures mapLEQ(m, r.m)
    ensures r.calid()
    ensures r.from(this)
  {

    assert  //the below should be a predicate (from MapKV)
      && k !in m.Keys
      && k !in m.Values
         //&& COK(k,m.Keys)
      && (forall oo <- k.AMFO - {k} :: oo in m.Keys)
         //&& (k.region.Heap? ==> m[k].region.Heap?)
      && (k.region.Heap? ==> k.region.owner in k.AMFO)
      && (k.region.Heap? ==> k.region.owner in m.Keys)
         //&& (k.region.Heap? ==> m[k.region.owner] == m[k].region.owner )
         //&& (forall oo <- k.AMFO :: m[oo] in m[k].AMFO)
      && (k.region.Heap? ==> k.extra <= k.AMFO)
      && (forall xo <- k.extra :: xo in m.Keys)
         //&& (forall xo <- k.extra :: m[xo] in m[k].extra)
      ;

    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    reveal calidOK();
    assert calidOK();

    assert ks == m.Keys;
    assert calidMap();
    reveal calidMap();
    assert calidSheep();
    reveal calidSheep();

    assert MapOK(m);
    assert CallOK(oHeap);

    assert AllMapEntriesAreUnique(m);

    var numap := MapKV(m,k,k);
    assert MapOK(numap);

    assert AllMapEntriesAreUnique(numap) by {
      reveal UniqueMapEntry();
      assert AllMapEntriesAreUnique(m);
      assert forall i <- m.Keys :: UniqueMapEntry(m, i);
      assert k !in m.Keys;
      assert k !in m.Values;
      //            assert forall i <- (m.Keys+{k}) :: UniqueMapEntry(m, i);
      assert forall i <- (m.Keys+{k}) :: UniqueMapEntry(numap, i);
      assert (m.Keys+{k}) == numap.Keys;
      assert forall i <- (numap.Keys) :: UniqueMapEntry(numap, i);
      assert AllMapEntriesAreUnique(numap);
    }


    var rv := Map(numap, ks+{k}, vs+{k}, o, oHeap, ns);

    assert rv == Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns);
    assert k in rv.ks && rv.m[k] == k;
    assert k in rv.m.Keys;
    assert k in rv.m.Values;
    assert MapOK(rv.m);
    assert weirdo() && (rv.m == MapKV(this.m,k,k));
    assert mapLEQ(m, rv.m);


    assert rv.calidObjects() by {
      assert
        && ks == m.Keys
        && vs == m.Values
        && o in oHeap
        && ks <= oHeap
        && ns !! oHeap

        && vs <= ns + oHeap
        ;
    }


    assert rv.calidOK() by {
      assert (rv.o in rv.oHeap);
      assert (rv.ks <= rv.oHeap);
      assert (rv.vs <= rv.oHeap+ns);
      assert COK(rv.o, rv.oHeap) by { assert COK(o,oHeap);  assert rv.oHeap == oHeap; assert rv.o == o; }
      assert CallOK(rv.oHeap)    by { assert CallOK(oHeap); assert rv.oHeap == oHeap; }
      assert CallOK(rv.ks, rv.oHeap) by { assert CallOK(ks, oHeap);
                                          assert COK(k,oHeap);
                                          CallOKfromCOK(k,oHeap);
                                          CallOKWiderFocus(ks,{k},oHeap);
                                          assert rv.oHeap == oHeap;
                                          assert rv.ks == ks+{k}; }
      assert CallOK(rv.vs, rv.oHeap+rv.ns) by { assert CallOK(vs, oHeap+ns);
                                                assert COK(k,oHeap);
                                                CallOKfromCOK(k,oHeap);
                                                CallOKWiderContext({k},oHeap,ns);
                                                CallOKWiderFocus(vs,{k},oHeap+ns);
                                                assert rv.oHeap+rv.ns == oHeap+ns;
                                                assert rv.vs == vs+{k}; }
      assert CallOK(rv.ns, rv.oHeap+rv.ns) by { assert CallOK(ns, oHeap+ns);
                                                assert rv.oHeap == oHeap;
                                                assert rv.ns == ns; }
      assert rv.calidOK();
    }

    reveal rv.calidMap();
    assert rv.calidMap() by {
      reveal calidObjects(); assert calidObjects();
      reveal calidOK(); assert calidOK();
      assert MapOK(m);
      assert k in rv.m.Keys;
      assert rv.m[k] == k;
      assert (forall x <- {k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
      assert (forall x <- {k}, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
      assert MapOK(rv.m);

    }
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    reveal rv.calidSheep();
    assert rv.ks == rv.m.Keys;
    reveal AreWeNotMen();
    assert (forall x <- rv.ks :: AreWeNotMen(x, rv));
    assert (forall x <- rv.ks :: x.fieldModes == rv.m[x].fieldModes);
    assert rv.calidSheep();
    reveal rv.calid();
    assert rv.calid();
    assert rv.from(this);

    rv
  }


  function nu(k : Object, v : Object) : set<Object>
  {
    if (k==v) then {} else {v}
  }

  lemma funu(k : Object, v : Object)
    ensures nu(k,v) <= {v}
  {}

  //     opaque function {:isolate_assertions} putIO(k : Object, v : Object := k) : (r : Map)
  //       //put k -> v into map, k inside o
  //       reads oHeap`fields, oHeap`fieldModes
  //       reads ns`fields, ns`fieldModes,  v`fields, v`fieldModes
  //
  //       requires calid()
  //       requires k  in oHeap
  //       requires k !in ks
  //       requires v  in oHeap+ns+nu(k,v)
  //       requires v !in vs
  //       requires COK(k, oHeap)
  //       requires COK(v, oHeap+ns+nu(k,v))
  //       requires ks <= oHeap
  //       requires k.owners() <= ks //hmm
  //       requires forall kx <- k.extra :: kx in ks
  //       requires forall kx <- k.extra :: m[kx] in v.extra
  //       requires v.fieldModes == k.fieldModes
  //
  //       requires if (k==v) then (v in oHeap) else (v !in oHeap)
  //
  //       ensures  r == Map(m[k:=v], ks+{k}, vs+{v}, o, oHeap, ns+nu(k,v))
  //       ensures  k in r.ks && r.m[k] == v
  //       ensures  COK(v, r.oHeap+r.ns)
  //       ensures  r.calid()   ///FIXFIXFIX
  //       ensures  r.from(this)
  // {
  //         var nukv := nu(k,v);
  //         var nv := ns+(nukv);
  //         var rv := Map(m[k:=v], ks+{k}, vs+{v}, o, oHeap, nv);
  //
  //         reveal COK();
  //         assert rv.oHeap+rv.ns == oHeap+ns+(nukv);
  //
  // ///        COKWiderContext(v, rv.oHeap+rv.ns, (newOrNothing((v==k),v))  );
  //
  //           assert  COK(v, rv.oHeap+nv) by
  //             {
  //                     assert COK(v, oHeap+nv);
  //                     assert rv.oHeap == oHeap;
  //                     assert rv.ns == ns+nukv;
  //                     assert COK(v, oHeap+ns+nukv);
  //                     assert rv.oHeap+rv.ns == oHeap+ns+nukv;
  //                     assert COK(v, rv.oHeap+rv.ns);
  //             }
  //
  // //random copied shit starts here
  //         assert oXn: oHeap !! ns by
  //         {
  //             assert calid(); reveal calid();
  //             assert calidObjects(); reveal calidObjects();
  //             assert
  //             && ks == m.Keys
  //             && vs == m.Values
  //             && o in oHeap
  //             && ks <= oHeap
  //             && ns !! oHeap
  //
  //             && vs <= ns + oHeap
  //             ;
  //         }
  //
  //           assert COK(v, rv.oHeap+rv.ns) by {
  //             assert COK(v, oHeap+ns+{v});  // from reqs
  //             assert rv.oHeap      == oHeap;
  //             assert rv.ns         == ns+nukv;
  //             assert rv.oHeap+rv.ns == oHeap+ns+nukv;
  //             assert COK(v, rv.oHeap+rv.ns);
  //           }
  //
  //           assert rv.calidObjects() by {
  //             reveal calid(), calidObjects();
  //             assert calid();
  //             assert calidObjects();
  //             reveal rv.calidObjects();
  //
  //             assert rv.ks == rv.m.Keys;
  //             assert rv.vs == rv.m.Values;
  //             assert rv.o in rv.oHeap;
  //             assert rv.ks <= rv.oHeap;
  //             assert    ns !!    oHeap by { reveal oXn; }
  //             assert rv.ns !! rv.oHeap by {
  //               assert  ns !! oHeap;
  //               assert rv.oHeap == oHeap;
  //               assert rv.oHeap !! ns;
  //               assert if (k==v)
  //                 then (v  in oHeap && (nukv=={ }) && ({ }!!oHeap))
  //                 else (v !in oHeap && (nukv=={v}) && ({v}!!oHeap));
  //               assert    rv.ns == ns+nukv;
  //               assert    oHeap !! nukv;
  //               assert rv.oHeap !! nukv;
  //               assert rv.oHeap !! ns + nukv;
  //               assert rv.oHeap !! rv.ns;
  //               }
  //             assert rv.vs <= rv.ns + oHeap;
  //
  //             assert rv.calidObjects();
  //           }
  //
  //           assert v !in vs; // from reqs
  //           assert vs == m.Values by {
  //             assert calid();
  //             reveal calid();
  //             assert calidObjects();
  //             reveal calidObjects();
  //             assert vs == m.Values;
  //                    }
  //           assert v !in m.Values;
  //
  //           assert rv.calidOK() by {
  //             reveal rv.calid(); assert calid();
  //             reveal rv.calidOK(); assert calidOK();
  //             reveal rv.calidObjects(); assert calidObjects();
  //             assert COK(o, oHeap);
  //             assert COK(rv.o, rv.oHeap);
  //             assert CallOK(rv.oHeap);
  //             CallOKfromCOK(k, oHeap);
  //             assert CallOK(ks, oHeap);
  //             CallOKtoSubset(ks, oHeap);
  //             CallOKWiderFocus(ks, {k}, oHeap);
  //             assert CallOK(rv.ks, rv.oHeap);
  //             assert oHeap+ns+{v} == rv.oHeap+rv.ns;
  //             assert COK(v, rv.oHeap+rv.ns);
  //             // CallOKWiderContext({v}, rv.oHeap, rv.ns);    //unneeded?
  //             // CallOKtoSubset(rv.vs, rv.oHeap+rv.ns);       //unneeded?
  //             assert rv.vs <= rv.ns + oHeap;
  //             assert CallOK(vs, oHeap+ns);
  //             CallOKWiderContext(vs, oHeap+ns, nukv);
  //             assert COK(v,oHeap+ns+nukv); //reqs
  //             CallOKfromCOK(v, oHeap+ns+nukv);   //could subsume within COK?> (or not0)
  //             CallOKWiderFocus(vs, {v}, oHeap+ns+{v});  //version just adding one?
  //             assert vs+{v}== rv.vs;
  //             assert CallOK(rv.vs, rv.oHeap+rv.ns);
  //             assert ns+nukv == rv.ns;
  //             CallOKWiderContext(ns,oHeap+ns,nukv);  //is it worth cobinging these also
  //             assert CallOK(ns,   oHeap+ns+nukv);
  //             assert CallOK({v},  oHeap+ns+nukv);
  //             assert CallOK(nukv, oHeap+ns+nukv);
  //             CallOKWiderFocus(ns,nukv,oHeap+ns+nukv);
  //             assert CallOK(ns+nukv, oHeap+ns+nukv);
  //             assert CallOK(rv.ns, rv.oHeap+rv.ns);
  //             reveal rv.calidOK(); assert rv.calidOK();
  //           }
  //
  //
  //           // reveal rv.calidMap();
  //           // assert rv.calidMap() by {
  //             assert MapOK(rv.m) by {
  //                 assert calid();
  //                 reveal calid();
  //                 assert calidObjects();
  //                 reveal calidObjects();
  //                 reveal calidMap();
  //                 assert calidMap();
  //                 assert MapOK(m);
  //                 assert COK(k, oHeap);
  //                 reveal COK();
  //                 assert rv.ks == ks + {k};
  //                 assert rv.m.Keys == m.Keys + {k};
  //
  //                 reveal rv.calidObjects();
  //                 assert rv.calidObjects();
  //
  //
  //
  //                 assert rv.m.Keys == rv.ks;
  //                 assert k.owners() <= ks;
  //
  //                 assert forall x <- m.Keys :: x.AMFO <= ks by {
  //                   assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys;
  //                 }
  //                 assert k.owners() <= ks;
  //               //  assert forall x <- m.Keys+{k} :: x.owner() <= ks;
  //                 assert forall x <- m.Keys+{k} :: x.AMFO <= ks+{k};
  //                 assert (ks+{k}) == m.Keys+{k} == rv.ks == rv.m.Keys;
  //                 assert forall x <- rv.m.Keys :: x.AMFO <= rv.m.Keys;
  //                 assert forall x <- rv.m.Keys, oo <- x.AMFO :: oo in rv.m.Keys;
  //
  //                 assert (forall x <- rv.m.Keys :: x.region.Heap? == rv.m[x].region.Heap?);
  //                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO);
  //                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in rv.m.Keys);
  //                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: rv.m[x.region.owner] == rv.m[x].region.owner );
  //
  //               assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);
  //               assert (forall x <- m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
  //               assert rv.m[k] == v;
  //               assert ks == m.Keys;
  //               assert (k.owners() <= ks);
  //               assert (k.AMFO - {k}) <= ks;
  //               assert (forall oo <- (k.AMFO - {k}):: oo in m.Keys);
  //               assert (forall oo <- (k.AMFO - {k}):: m[oo] in v.AMFO);
  //               assert (forall oo <- (k.AMFO - {k}):: rv.m[oo] in rv.m[k].AMFO);
  //
  //               assert (forall x <- m.Keys, xo <- x.extra :: xo in m.Keys);
  //               assert (forall x <- m.Keys, xo <- x.extra :: m[xo] in m[x].extra);
  //               assert (forall x <- m.Keys, xo <- x.extra :: xo in rv.m.Keys);
  //               assert (forall x <- m.Keys, xo <- x.extra :: rv.m[xo] in rv.m[x].extra);
  //
  //
  //
  //               assert (forall xo <- k.extra :: xo in rv.m.Keys);
  //               assert (forall xo <- k.extra :: rv.m[xo] in rv.m[k].extra);
  //
  //                 assert rv.m.Keys == m.Keys + {k};
  //
  //                 assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
  //                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.extra <= x.AMFO);
  //                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.extra <= rv.m.Keys);
  //                 assert (forall x <- rv.m.Keys, xo <- x.extra :: xo in rv.m.Keys);
  //                 assert (forall x <- rv.m.Keys, xo <- x.extra :: rv.m[xo] in rv.m[x].extra);
  //             }  //MAapOK
  //
  //
  //
  //             reveal rv.calidObjects();
  //             assert ks == m.Keys;
  //             assert rv.ks == rv.m.Keys;
  //             assert (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
  //             assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
  //             assert (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO);
  //             reveal rv.calidMap();
  //             assert rv.calidMap();
  //
  //                 reveal rv.calidSheep();
  //                 reveal rv.calidObjects();
  //                 assert ks == m.Keys;
  //                 assert rv.ks == rv.m.Keys;
  //             assert inside(k, o);
  //             reveal calidMap();
  //             assert calidMap();
  //             reveal calidSheep();
  //
  //
  //             assert forall x <- ks :: AreWeNotMen(x, this);
  //             assert rv.ks == rv.m.Keys == (ks+{k});
  //
  //             assert forall x <- ks :: x.fieldModes == m[x].fieldModes;
  //             assert k.fieldModes == v.fieldModes;
  //             assert forall x <- rv.ks :: x.fieldModes == rv.m[x].fieldModes;
  //
  //             assert calidSheep();
  //             reveal rv.calidSheep();
  //             //reveal UniqueMapEntry();
  //
  //             assert ks == m.Keys;
  //
  //                 reveal AreWeNotMen();
  //                 reveal UniqueMapEntry();
  //             assert forall x <- ks  :: AreWeNotMen(x, this);
  //             assert forall x <- {k} :: AreWeNotMen(x, rv);
  //             assert forall x <- rv.m.Keys :: AreWeNotMen(x, rv);
  //
  //             assert rv.calidSheep();
  //             reveal rv.calid(); assert rv.calid();
  // ///////random copied shit ends here
  //
  //
  //             reveal rv.calidOK();
  //             assert rv.calidOK();
  //             reveal rv.calidObjects();
  //             assert rv.calidObjects();
  //             reveal rv.calidMap();
  //             assert rv.calidMap();
  //             reveal rv.calidSheep();
  //             assert rv.calidSheep();
  //
  //             reveal rv.calid();
  //             assert rv.calid();
  //
  //         rv
  // }




















































  predicate weirdo()
    requires calid()
    ensures  MapOK(m)
    ensures  AllMapEntriesAreUnique(m)
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
  {
    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    assert ks == m.Keys;
    reveal calidMap();
    assert calidMap();
    assert MapOK(m);
    DevoIsUnique();
    assert AllMapEntriesAreUnique(m);
    MapOK(m) &&  AllMapEntriesAreUnique(m)
  }



  opaque predicate {:onlyNUKE} AreWeNotMen(x : Object,  rv : Map)  //hmmm wgt etc?
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires x in rv.m.Keys
  {
    && (   (inside(x,rv.o)) ==> rv.m[x] in rv.ns)
    && (not(inside(x,rv.o)) ==> (rv.m[x] == x))
    && (   (inside(x,rv.o)) ==> (UniqueMapEntry(rv.m,x)))
    && (not(inside(x,rv.o)) ==> (UniqueMapEntry(rv.m,x)))
  }

  lemma WeAreDevo()
    requires calid()
    ensures  forall k <- m.Keys :: AreWeNotMen(k,this)
  {
    reveal calid();
    assert calid();
    reveal calidOK();
    assert calidOK();
    reveal calidObjects();
    assert calidObjects();
    reveal calidMap();
    assert calidMap();
    reveal calidSheep();
    assert calidSheep();

    assert  forall k <- m.Keys :: AreWeNotMen(k,this);
  }

  lemma DevoIsUnique()
    requires calid()
    ensures  forall k <- m.Keys :: UniqueMapEntry(m, k)
    ensures  AllMapEntriesAreUnique(m)
  {
    reveal calid();
    assert calid();
    reveal calidOK();
    assert calidOK();
    reveal calidObjects();
    assert calidObjects();
    reveal calidMap();
    assert calidMap();
    reveal calidSheep();
    assert calidSheep();
    reveal AreWeNotMen();

    WeAreDevo();

    assert  forall k <- m.Keys :: AreWeNotMen(k,this);

    assert  forall k <- m.Keys :: (   (inside(k,o)) ==> (UniqueMapEntry(m,k)));
    assert  forall k <- m.Keys :: (not(inside(k,o)) ==> (UniqueMapEntry(m,k)));
    assert  forall k <- m.Keys :: (                     (UniqueMapEntry(m,k)));
  }





  static lemma AintNoSunshine(x : Object, rv : Map)
    //
    requires not(inside(x,rv.o))
    requires x !in rv.m.Keys

    requires rv.calid()
    requires forall k <- rv.m.Keys :: rv.AreWeNotMen(k,rv)
    requires x  in rv.oHeap
    requires x !in rv.ns

    ensures  x !in rv.m.Values
  {
    assert rv.calid();

    reveal rv.calid();
    assert rv.calid();
    reveal AreWeNotMen();
    assert forall k <- rv.m.Keys :: rv.AreWeNotMen(k,rv);

    reveal rv.calidObjects();
    assert rv.calidObjects();
    reveal rv.calidOK();
    assert rv.calidOK();
    reveal rv.calidMap();
    assert rv.calidMap();
    reveal rv.calidSheep();
    assert rv.calidSheep();


    forall k <- rv.m.Keys
      ensures (x !in rv.m.Values)
    {
      if (inside(k,rv.o))
      { assert rv.AreWeNotMen(k, rv);
        assert (rv.m[k] in rv.ns);
        assert  x !in rv.ns;
        assert (rv.m[k] != x);
      }
      else if (k != x)
      {
        assert not(inside(k,rv.o));
        assert rv.AreWeNotMen(k, rv);
        assert (rv.m[k] == k);
        assert  rv.m[k] != x;
      }
      else
      {
        assert k in rv.m.Keys;
        assert {:contradiction} k == x;
        assert {:contradiction} not(inside(k,rv.o));
        assert {:contradiction} rv.AreWeNotMen(k, rv);
        assert {:contradiction} rv.m[k] == k;
        assert {:contradiction} rv.m[k] == x;
        assert {:contradiction} rv.m[x] == x;
        assert {:contradiction} x in rv.m.Values;
        assert {:contradiction} x in rv.m.Keys;
        assert {:contradiction} false;
      }
    }
  }


  twostate predicate calid2()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
  {
    old( calid() )
  }

  opaque predicate calid() : (r : bool)
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes

    ensures r ==> (ks == m.Keys)
    ensures r ==> (vs == m.Values)
  {
    reveal calidObjects();

    && calidObjects()
    && calidOK()
    && calidMap()
    && calidSheep()
  }

  opaque predicate  {:onlyNUKE} calidObjects()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
  {
    && ks == m.Keys
    && vs == m.Values

    && o in oHeap
    && ks <= oHeap
    && ns !! oHeap

    && vs <= ns + oHeap

    && ns <= vs
       //&& ns == vs + oHeap //or is this wshat I mean?
  }

  opaque predicate  {:onlyReadFrames} calidOK()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
  {
    && (o in oHeap)
    && (ks <= oHeap)
    && (vs <= oHeap+ns)
    && COK(o, oHeap)
    && CallOK(oHeap)
    && CallOK(ks, oHeap)
    && CallOK(vs, oHeap+ns)
    && CallOK(ns, oHeap+ns)
  }


  opaque predicate  {:onlyNUKE} calidMap()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calidObjects() && calidOK()
  {
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    && AllMapEntriesAreUnique(m)
    && MapOK(m) // potentiall should expand this out?
    && (forall x <- ks :: (not(inside(x,o)) ==> (m[x] == x)))
    && (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO)
  }

  opaque predicate  {:onlyNUKE} calidSheep2()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calidObjects() && calidOK() && calidMap()
  {
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    reveal calidMap(); assert calidMap();
    assert ks == m.Keys;

    && (forall x <- ks ::
          if (inside(x,o))
          then ((m[x] in ns) && (UniqueMapEntry(m,x)))
          else ((m[x] == x)  && (UniqueMapEntry(m,x))))
    && (forall x <- ks :: x.fieldModes == m[x].fieldModes)
  }


  opaque predicate {:onlyNuke} calidSheep()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calidObjects() && calidOK()// && calidMap()
  {
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    //reveal calidMap(); assert calidMap();
    assert ks == m.Keys;

    reveal AreWeNotMen();
    //reveal UniqueMapEntry();

    && (forall x <- ks :: AreWeNotMen(x, this))
    && (forall x <- ks :: x.fieldModes == m[x].fieldModes)
    && AllMapEntriesAreUnique(m)
  }



  opaque predicate {:onlyNUKE} calidSheep3()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calidObjects() && calidOK() && calidMap()
  {
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    reveal calidMap(); assert calidMap();
    assert ks == m.Keys;

    && (forall x <- ks |    (inside(x,o)) :: (m[x] in ns))
    && (forall x <- ks |    (inside(x,o)) :: (UniqueMapEntry(m,x)))
    && (forall x <- ks | not(inside(x,o)) :: (m[x] == x))
    && (forall x <- ks | not(inside(x,o)) :: (UniqueMapEntry(m,x)))
    && (forall x <- ks :: x.fieldModes == m[x].fieldModes)
    && AllMapEntriesAreUnique(m)
  }





  lemma {:onlyNUKE} sheep12()
    requires calidObjects() && calidOK() && calidMap()
    requires calidSheep2()
    ensures  calidSheep()
  {
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    reveal calidMap(); assert calidMap();
    reveal calidSheep(), calidSheep2();
    assert calidSheep2();

    assert forall x <- ks ::
        if (inside(x,o))
        then ((m[x] in ns) && (UniqueMapEntry(m,x)))
        else ((m[x] == x))//  && (UniqueMapEntry(m,x)))
      ;

    reveal AreWeNotMen();
    assert forall x <- ks :: AreWeNotMen(x, this);

    assert forall x <- ks :: x.fieldModes == m[x].fieldModes;

  }

} ///end datatype Map



lemma SubsetOfKeysOfExtendedMap(subset : set<Object>, left : Map, right : Map)
  requires left.calid()
  requires right.calid()
  requires subset <= left.ks
  requires mapLEQ(left.m, right.m)
  ensures  subset <= right.ks
{
  reveal Map.calid();
  reveal Map.calidObjects();
  assert left.calid();
  assert right.calid();
  assert left.calidObjects();
  assert right.calidObjects();
  assert mapLEQ(left.m, right.m);
  assert left.m.Keys <= right.m.Keys;
  assert subset <= left.ks <= right.ks;
}


lemma Yowl(k : Object, kk : set<Object>)
  requires forall kx <- k.extra :: kx in kk
  ensures  k.extra <= kk
{}


lemma Howl(k : Object, kk : set<Object>)
  requires k.extra <= kk
  ensures  forall kx <- k.extra :: kx in kk
{}



///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
//actual cloning methods


method Clone_Via_Map(a : Object, m' : Map)
  returns (b : Object, m : Map)
  //entry point for Clone - clones a according to map m'
  //call with m' empty
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 20 //Clone_Via_Map

  requires m'.calid()
  requires a in m'.oHeap  //technically redundant given COKx
  requires COK(a, m'.oHeap)

  //extraOK  requires a.extra == {} //extra not yet cloned               HERE

  //ensures  (m.oHeap - m.ks) < (m'.oHeap - m'.ks)

  ensures  m.calid()
  //includes CallOK(m.oHeap)
  //includes CallOK(m.ks, m.oHeap)
  //ensures  a.region.Heap? == b.region.Heap?

  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b,m.oHeap+m.ns)

  //should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.from(m')

  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
  //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
  ensures  MapOK(m.m)
  ensures  a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures  a.extra <= m.ks //ditto?    //tis weird, better to ensures COK(a,m.ks)?   or even k.hasK(a) is enough?
  // should we say something about b.AMFO?  b.AMFO <= m.vs? por again m.hasV(b)?
  // m.key(a)?  m.val(a)???
  ensures  m.from(m')
  //ensures b.AMFO == set x <- a.AMFO :: m.m[x]


  // ensures  a !in m'.ks ==> b !in m'.ns  //KJX sure about this?
  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.ns)



  ensures b.fieldModes == a.fieldModes

  //  ensures  fresh(b)
  //modifies m'[a]
  //  modifies m'.ns`fields //argh. pity so wide
  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  // modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  modifies {} // only modifes objecst allocated aftrer this point?
{
  m := m';

  assert m.calid();

  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns    >= m'.ns;

  assert unchanged(a) && unchanged(m.oHeap);

  print "CALL Clone_Via_Map:", fmtobj(a), " owner:", fmtobj(m.o), "\n";

  print "VARIANT CVM ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 20, "\n";

  assert COKSTART: COK(a, m.oHeap);

  print "Clone_Via_Map started on:", fmtobj(a), "\n";

  //if already in hash table - return it and be done!
  //not sure why this takes sooo long compared to other
  if (a in m.ks) {

    assert (a in m.m.Keys) by {
      reveal m.calid();
      assert m.calid();
      reveal m.calidObjects();
      assert m.calidObjects();
      assert m.ks == m.m.Keys;
    }

    b := m.m[a];

    assert (b in m.vs) by {
      reveal m.calid();
      assert m.calid();
      reveal m.calidObjects();
      assert m.calidObjects();
      assert b == m.m[a];
      assert b in m.m.Values;
      assert m.vs == m.m.Values;
      assert b in m.vs;
    }

    assert CallOK(m.vs, m.oHeap+m.ns) by
    {
      reveal m.calid();
      assert m.calid();
      reveal m.calidObjects();
      assert m.calidObjects();
      reveal m.calidOK();
      assert m.calidOK();
    }

    COKfromCallOK(b, m.vs, m.oHeap+m.ns);
    assert COK(b, m.oHeap+m.ns);
    print "RETN Clone_Via_Map: ", fmtobj(a)," already cloned,  returning ",fmtobj(b), "\n";



    assert MapOK(m.m) && (a.AMFO <= m.ks) && (a.extra <= m.ks)  by
    {
      reveal m.calid();
      assert m.calid();
      reveal m.calidOK();
      assert m.calidOK();
      reveal m.calidObjects();
      assert m.calidObjects();
      reveal m.calidMap();
      assert m.calidMap();
      assert m.ks == m.m.Keys;
      assert MapOK(m.m) && a.AMFO <= m.m.Keys;
      assert MapOK(m.m) && a.AMFO <= m.ks;
      assert a.extra <= m.ks;
    }

    reveal m.calid();
    assert m.calid();
    reveal m.calidSheep();
    assert m.calidSheep();

    assert  b.fieldModes == a.fieldModes;
    assert  m.o     == m'.o;
    assert  m.oHeap == m'.oHeap;
    assert  m.ns    >= m'.ns;
    //  reveal  m.from();
    return;
  } // a in ks, already cloned

  assert unchanged(a) && unchanged(m.oHeap);

  assert a !in m.ks;
  assert a !in m'.ks;

  // assert a !in m.vs;
  // assert a !in m'.vs;

///case analysis...
  if (outside(a,m.o)) {
    print "Clone_Via_Map ", fmtobj(a), " is really outside ", fmtobj(m.o), "so maps to itself (share not clone)\n";

    if (a.region.Heap?) {
      print "Clone_Via_Map outside owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";

      assert
        && (a !in m.m.Keys)
        && (a !in m.ns)
        && (m.m.Values == m.vs)
      by {
        reveal m.calid();
        assert m.calid();
        reveal m.calidOK();
        assert m.calidOK();
        reveal m.calidObjects();
        assert m.calidObjects();
        reveal m.calidMap();
        assert m.calidMap();
        assert m.ks == m.m.Keys;
        reveal m.calidSheep();
        assert m.calidSheep();
        assert a !in m.m.Keys;
        assert a in m.oHeap;
        assert m.oHeap !! m.ns;
        assert a in m.oHeap;
        assert m.m.Values == m.vs;
      }

      m.WeAreDevo();
      Map.AintNoSunshine(a,m);

      assert a !in m.vs by {
        assert a !in m.m.Values;
        assert m.m.Values == m.vs;
        assert a !in m.vs;
      }
      b, m := Clone_Outside_Heap(a, m);

      // assert a !in m'.ks ==> b !in m'.ns;   //KJX sure about this?

      //END outside  HEAP OBJECT
    }
    else
    {
      print "Clone_Via_Map world:", fmtobj(a),"\n";

      b, m := Clone_Outside_World(a, m);

      // assert a !in m'.ks ==> b !in m'.ns;   //KJX sure about this?

    }//end of outside / world

    assert m.m[a] == b;

    assert  m.o     == m'.o;
    assert  m.oHeap == m'.oHeap;
    assert  m.ns    >= m'.ns;

    assert m.calid();
    reveal m.calid();
    assert m.calidObjects();
    assert m.calidOK();
    reveal m.calidSheep();
    assert m.calidSheep();

    assert a in m.ks;
    assert b.fieldModes == a.fieldModes;

    assert forall kx <- a.extra :: m.m[kx] in m.m[a].extra;
    assert a.extra <= m.ks;

    // assert a !in m'.ks ==> b !in m'.ns;   //KJX sure about this?

    return;  //we may as well just return here.
             //we've done all we need to do.  I think.

  }///END OF THE OUTSIDE CASE
  else
  { //start of the Inside case

    if (a.region.Heap?) {  //start of inside heap case
      print "Clone_Via_Map owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";

      b, m := Clone_Inside_Heap(a, m);
      //  assert b.fields.Keys == {};  //we now do clone fields though!!

      // assert a !in m'.ks ==> b !in m'.ns;   //KJX sure about this?

      //END inside HEAP OBJECT
    } else {
      //inside "world"" OBJECT

      b, m := Clone_Inside_World(a, m);
      //  assert b.fields.Keys == {};

      // assert a !in m'.ks ==> b !in m'.ns;   //KJX sure about this?
    }   //end of inside world heap case
  } //end of inside case


  ///////////////////////////////////////////////////////////////
  //tidying up after the cases..

  // assert a !in m'.ks ==> b !in m'.ns;   //KJX sure about this?

  reveal m.calid();
  assert m.calid();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidOK();
  assert m.calidOK();
  assert CallOK(m.vs, m.oHeap+m.ns);
  assert b in m.m.Values;
  assert m.m.Values == m.vs;
  assert b in m.vs;
  COKfromCallOK(b, m.vs, m.oHeap+m.ns);
  assert COK(b, m.oHeap+m.ns);
  //  assert fresh(b);   //umm, yeah should probalboy be fresh at least if INSIDE, but...
  //  have to experiment with a clause somewhere in calidSheep saying every inside clone is new
  //  or everyhing in ns is new. or...
  assert b in m.ns;

  assert m.m[a] == b;
  assert a !in m'.ks;
  assert b !in m'.oHeap;
  //assert b !in m'.ns;


  //  assert  b.fields.Keys == {};

  assert  b.fieldModes.Keys == a.fieldModes.Keys;

  reveal m.calidSheep();
  assert m.calidSheep();

  assert  b.fieldModes == a.fieldModes;

  //  assert a !in m'.ks ==> b !in m'.ns;   //KJX sure about this?

  //  assert m.from(m') by {
  //      reveal m.from();
  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns    >= m'.ns;

  assert m.from(m');
  //  }
}







method Clone_All_Fields(a : Object, b : Object, m' : Map)
  returns (m : Map)
  //clone field a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases (m'.oHeap - m'.ks +{a}), a.AMFO, (a.fields.Keys), 10 //Clone_All_Fields

  requires MPRIME: m'.calid()
  requires COK(a, m'.oHeap)
  requires COK(b, m'.oHeap+m'.ns)

  requires b.fields.Keys == {}

  requires a.fields.Keys <= a.fieldModes.Keys
  requires a.fieldModes == b.fieldModes


  requires a in m'.oHeap
  requires a in m'.ks

  requires b in m'.vs
  requires b in m'.ns
  requires (a in m'.m.Keys) && m'.m[a] == b
  requires m'.o    in m'.oHeap
  requires m'.ks   <= m'.oHeap

  requires a.AMFO <= m'.ks  //seems weird but we are populating m, right...
  requires a.extra <= m'.ks //ditto?

  // requires b.fieldModes[n] == Evil //evilKJX this is actually evil
  //well not *that* evil as I still must satisfy refOK
  //
  // requires forall n <- b.fields :: (n in b.fieldModes) &&
  //             AssignmentCompatible(b, b.fieldModes[n], b.fields[n])

  //consequently
  //   requires refOK(a, a.fields[n])
  requires a.region.Heap? == b.region.Heap?

  ensures  m.calid()
  ensures  old(m'.calid())
  ensures  MapOK(m.m)
  ensures  a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures  a.extra <= m.ks //ditto?

  ensures  b.fields.Keys == a.fields.Keys

  ensures  a in m.ks
  ensures  (a in m.m.Keys) && m.m[a] == b



  //   ensures  n in b.fields
  //   ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]

  ensures  b in m.vs

  ensures  mapLEQ(m'.m,m.m)

  ensures  CallOK(m.oHeap)
  ensures  COK(a, m.oHeap)
  ensures  COK(b, m.oHeap+m.ns)
  ensures  CallOK(m.vs, m.oHeap+m.ns)
  ensures  CallOK(m.ns, m.oHeap+m.ns)

  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns    >= m'.ns
  ensures  m.ks    <= m.oHeap

  ensures a.fieldModes == b.fieldModes
  ensures b.fields.Keys == a.fields.Keys

  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.ns - {b})  //will this work?

  ensures  forall x <- (m.vs - {b}) :: old(allocated( x )) ==> unchanged( x ) //duesb;t veruft....

  //  modifies (set o : Object | o !in m'.oHeap)`fields
  // modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns?
  modifies b`fields   ///GGRRR
{
  m := m';

  assert m'.calid() by { reveal MPRIME; }

  assert BINNS:  b in m.ns;
  print "VARIANT CAF ", |(m'.oHeap - m'.ks +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";
  print "<<<<<<<<<<<\n";
  print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
  print "<<<<<<<<<<<\n";


  assert unchanged(a) && unchanged(m.oHeap);

  assert  m.o == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns == m'.ns;
  assert  m.vs == m'.vs;

  assert  m.ks == m'.ks;
  assert  a in m'.ks;

  assert m.m[a] == b;  //mmmKJX
  // assert (a in m.ks) ==> (m[a] == b);  //mmmKJX

  assert m.calid();
  assert m'.calid() by { reveal MPRIME; }
  assert COK(b, m.oHeap+m.ns);
  assert HEREB: COK(b, m.oHeap+m.ns);




  //assert fresh(b);
  assert  b.fields.Keys == {};
  assert b in m.vs;

  //START OF FIELDS…

  print "<<<<<<<<<<<\n";
  printmapping(m.m);
  print "<<<<<<<<<<<\n";

  assert m.calid();
  assert m'.calid() by { reveal MPRIME; }

  var ns : seq<string> := set2seq(a.fields.Keys);

  assert forall k <- a.fields.Keys :: (multiset(a.fields.Keys))[k] == 1;
  assert forall s <- ns :: (multiset(ns))[s] == 1;
  assert forall i | 0 <= i < |ns|, j | 0 <= j < |ns| :: (ns[i] == ns[j]) <==> i == j;
  //assert b.fields.Keys == {};
  assert b.fields.Keys == seq2set(ns[..0]);


  print "Clone_All_Fields fields:", fmtobj(a), " fields=", fmtseqstr(ns), "\n";

  //DOING FIELDS≈≈

  print "BLOOP BLOOP BLOOP\n";

  assert m.calidOK() by {
    assert m.calid();
    reveal m.calid();
    assert m.calidOK();
  }

  assert COK(b, m.oHeap+m.ns);

  assert m'.calid() by { reveal MPRIME; }

  label BLOOP:

  assert m.calidOK();
  reveal m.calidOK();
  assert m.calid();
  assert CallOK(m.ns, m.oHeap+m.ns);
  assert CallOK(m.vs, m.oHeap+m.ns);

  assert CallOK(m.ks, m.oHeap) by {}



  var rm := m;

  assert  rm.o     == m.o      == m'.o;
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns;
  assert  rm.vs    >= m.vs     >= m'.vs;
  assert  m.ks     <= rm.ks    <= m.oHeap;


  COKgetsDeclaredFields(a, m.oHeap);
  assert unchanged(a) && unchanged(m.oHeap);
  assert CallOK(m.ks, m.oHeap);


  for i := 0 to |ns|

    invariant  rm.o     == m.o      == m'.o
    invariant  rm.oHeap == m.oHeap  == m'.oHeap
    invariant  rm.ns    >= m.ns     >= m'.ns
    invariant  rm.vs    >= m.vs     >= m'.vs
    invariant   m.ks    <= rm.ks    <= m.oHeap

    invariant  b in m.ns
    invariant  b in m.vs

    invariant COK(a, m.oHeap)
    invariant COK(b, m.oHeap+m.ns)
    invariant mapLEQ(m'.m,m.m)
    invariant a in m.oHeap
    invariant a in m.ks
    invariant m.o in m.oHeap
    invariant CallOK(m.oHeap)
    invariant CallOK(m.ks, m.oHeap)
    invariant CallOK(m.ns, m.oHeap+m.ns)
    invariant CallOK(m.vs, m.oHeap+m.ns)
    invariant m.calid()
    invariant old(m'.calid())

    invariant unchanged(a)
    invariant unchanged(m.oHeap)
    //invariant forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.at(x) == x))
    invariant (m'.oHeap - m'.ks +{a}) >= (m.oHeap - m.ks +{a})
    invariant (m'.oHeap - m'.ks) >= (m.oHeap - m.ks)
    invariant b.fields.Keys == seq2set(ns[..i])
    invariant forall i | 0 <= i < |ns|, j | 0 <= j < |ns| :: (ns[i] == ns[j]) <==> i == j

    invariant  m.m[a] == b
    invariant  a.fieldModes == b.fieldModes
    invariant  a.AllFieldsAreDeclared()


    invariant old(m'.calid())
  {

    assert b.fields.Keys == seq2set(ns[..i]);

    assert COK(b, m.oHeap+m.ns);

    var n : string := ns[i];
    var ofv : Object := a.fields[n];

    assert n !in seq2set(ns[..i]);

    assert (n !in b.fields.Keys) by {
      assert n !in seq2set(ns[..i]);
      assert b.fields.Keys == seq2set(ns[..i]);
      assert (n !in b.fields.Keys);
    }

    print "  TLOOP  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
    print "  TLOOP  (recurse on field ",n,")\n";
    print "  TLOOP m:", |m.oHeap - m.ks|, " m':", |m'.oHeap - m'.ks|, "\n";
    print "  TLOOP b.fieldsKeys==", b.fields.Keys, "\n";
    print "  TINV                ", ns[..i], "\n";
    print "  TLOOPINV            ",seq2set(ns[..i]),"\n";


    print "VARIANT*CAF ", |(m'.oHeap - m'.ks +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";


    //   assert (m.oHeap - m.ks) < (m'.oHeap - m'.ks);

    assert  rm.o     == m.o      == m'.o;
    assert  rm.oHeap == m.oHeap  == m'.oHeap;
    assert  rm.ns    >= m.ns     >= m'.ns;
    assert  rm.ks    >= m.ks     >= m'.ks;
    assert  rm.vs    >= m.vs     >= m'.vs;
    assert  m.ks     <= rm.ks    <= m.oHeap;

    assert b in m.ns by { reveal BINNS; assert b in m.ns; }
    assert n !in b.fields;
    assert refOK(a, a.fields[n])
    by {
      assert m.calid();  reveal m.calid();
      assert m.calidOK(); reveal m.calidOK();
      assert COK(a,m.oHeap); reveal COK();
      assert a.AllOutgoingReferencesAreOwnership(m.oHeap);
      assert  refOK(a, a.fields[n]);
      // - inside(f,t.region.owner);
    }

    assert a.AllFieldsAreDeclared();
    assert a.fields.Keys <= a.fieldModes.Keys;
    assert a.fieldModes == b.fieldModes;
    assert n in b.fieldModes;


    assert forall n <- b.fields ::
        && (n in b.fieldModes)
        && AssignmentCompatible(b, b.fieldModes[n], b.fields[n])
    by {
      assert m.calid();
      reveal m.calid();

      assert old(m'.calid());

      assert COK(b, m.oHeap+m.ns);
      reveal COK();
      assert b.Valid();
      assert b.AllFieldsContentsConsistentWithTheirDeclaration();
      assert forall n <- b.fields ::
          AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
    }

    var OLDFLDS := b.fields.Keys;

    assert b in m.ns;
    assert b in m.vs;
    assert a in m.ks;



    var v_caf := ((m'.oHeap - m'.ks +{a}), a.AMFO, (a.fields.Keys), 10);
    var v_cfm := ((m.oHeap - m.ks +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map

    print "v_caf ", v_caf, "\n";
    print "v_cfm ", v_cfm, "\n";

    assert b.fields.Keys == seq2set(ns[..i]);
    assert a.fields.Keys == seq2set(ns);

    print "okaoka ", (m'.oHeap - m'.ks +{a}) >  (m.oHeap - m.ks +{a}), "\n";
    print "okaoka ", (m'.oHeap - m'.ks +{a}) == (m.oHeap - m.ks +{a}), "\n";

    assert (m'.oHeap - m'.ks +{a}) >= (m.oHeap - m.ks +{a});
    assert a.AMFO >= a.AMFO;
    assert (a.fields.Keys) >= (a.fields.Keys - b.fields.Keys);
    assert 10 > 5;

    label B4CLONEFIELD:

    assert  old(m'.calid());



    rm := Clone_Field_Map(a,n,b,m);

    assert  old(m'.calid());

    assert  rm.o     == m.o      == m'.o;
    assert  rm.oHeap == m.oHeap  == m'.oHeap;
    assert  rm.ns    >= m.ns     >= m'.ns;
    assert  rm.ks    >= m.ks     >= m'.ks;
    assert  rm.vs    >= m.vs     >= m'.vs;
    assert  m.ks     <= rm.ks    <= m.oHeap;

    //   assert old@B4CLONEFIELD(forall x <- m'.ks :: x.fieldModes == m'.m[x].fieldModes);
    //   assert (forall x <- m'.ks :: x.fieldModes == old@B4CLONEFIELD(x.fieldModes));
    //   assert (forall x <- m'.ks :: m'.m[x].fieldModes == old@B4CLONEFIELD(m'.m[x].fieldModes));
    //   assert (forall x <- m'.ks :: x.fieldModes == m'.m[x].fieldModes);
    //


    assert b.fields.Keys == OLDFLDS + {n};

    assert rm.from(m);
    //assert m.from(m');
    //assert rm.from(m');

    assert b.fields.Keys == seq2set(ns[..i+1]);

    assert rm.calid();
    //  assert COK(b, m.oHeap+m.ns);
    m := rm;
    assert m.calid();
    assert old(m'.calid());

    //  by {
    //    reveal MPRIME; reveal m.calid();
    //
    //    assert m' == m';
    //    assert mapLEQ(m'.m, m.m);
    //
    //    assert forall k <- m'.m.Keys :: m'.m[k] == m.m[k];
    //    assert forall k <- m'.m.Keys :: m'.m[k].fields == m.m[k].fields;
    //    assert forall k <- m'.m.Keys :: m'.m[k] == m.m[k];
    //    assert forall k <- m'.m.Keys :: m'.m[k].fields == m.m[k].fields;
    //
    //             reveal m'.calid();
    // //            assert m'.calid();
    //
    //         assert (m'.o in  m'.oHeap);
    //         assert (m'.ks <= m'.oHeap);
    //         assert (m'.vs <= m'.oHeap+m'.ns);
    //         assert COK(m'.o, m'.oHeap);
    //         assert CallOK(m'.oHeap);
    //         assert CallOK(m'.ks, m'.oHeap);
    //
    //         assert CallOK(m'.vs-{b}, m'.oHeap+m'.ns) by
    //           {
    //
    //           }
    //
    //         assert CallOK(m'.ns-{b}, m'.oHeap+m'.ns) by
    //           {
    //
    //           }
    //
    //         // assert CallOK(m'.vs, m'.oHeap+m'.ns);
    //         // assert CallOK(m'.ns, m'.oHeap+m'.ns);
    //
    //             reveal m'.calidOK();
    //             assert m'.calidOK();
    //             reveal m'.calidObjects();
    //             // assert m'.calidObjects();
    //             reveal m'.calidMap();
    //             // assert m'.calidMap();
    //             assert m'.ks == m'.m.Keys;
    //
    //         reveal m'.AreWeNotMen();
    //         //reveal UniqueMapEntry();
    //
    //         assert (forall x <- m'.ks :: m'.AreWeNotMen(x, m'));
    //         assert (forall x <- m'.ks :: x.fieldModes == m'.m[x].fieldModes);
    //         assert AllMapEntriesAreUnique(m'.m);
    //
    //             reveal m'.calidSheep();
    //             assert m'.calidSheep();
    //
    //    assert m'.calid(); }
    //

    //assert rm.fromold(m');

    assert  CallOK(m.ks, m.oHeap)
    by { reveal m.calid();    assert m.calid();
         reveal m.calidOK();  assert m.calidOK();
       }


  } //end of loop

  assert unchanged(a) && unchanged(m.oHeap);


  //DONE FIELDS
  print "RETN Clone_All_Fields done ", fmtobj(a), "\n";

  assert COK(b, m.oHeap+m.ns) by { reveal HEREB; }
  assert mapLEQ(m'.m,m.m);
  //
  // assert m'.calid() by { reveal MPRIME; }

  reveal m.calid();
  assert m.calid();
  reveal m.calidObjects();
  assert m.calidObjects();

  reveal m.calidMap(); assert m.calidMap();
  reveal m.calidSheep(); assert m.calidSheep();


  assert m.m[a] == b;

  assert m.at(a) == b;
  assert a in m.ks;
  assert b in m.oHeap+m.ns;

  assert COK(b, m.oHeap+m.ns);

  assert mapLEQ(m'.m,m.m);


  assert CallOK(m.oHeap);
  assert COK(a, m.oHeap);
  assert COK(b, m.oHeap + m.ns);
  assert CallOK(m.vs, m.oHeap+m.ns);
  assert COK(b, m.oHeap  + m.ns);


  reveal m.calidObjects(); assert m.calidObjects();


  assert COK(m.o, m.oHeap);
  assert CallOK(m.oHeap);
  assert CallOK(m.ks, m.oHeap);
  assert CallOK(m.vs, m.oHeap+m.ns);
  assert CallOK(m.ns, m.oHeap+m.ns);

  reveal m.calidOK(); assert m.calidOK();

  reveal m.calidMap(); assert m.calidMap();

  assert MapOK(m.m);



  assert  rm.o     == m.o      == m'.o;
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns;
  assert  rm.vs    >= m.vs     >= m'.vs;

  reveal m.calidObjects(); assert m.calidObjects();
  reveal m.calidOK(); assert m.calidOK();
  reveal m.calidSheep(); assert m.calidSheep();

  assert m.ks == m.m.Keys;

  reveal m.AreWeNotMen();
  assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
  assert forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.m[x] == x));

  assert  b.fieldModes == a.fieldModes;

  reveal m.calid(); assert m.calid();

  // assert m'.calid() by { reveal MPRIME; }

  assert MapOK(m.m) && a.AMFO <= m.ks;
  assert unchanged(a) && unchanged(m.oHeap);
  //
  //     assert m'.calid() by {
  //        assert unchanged(m'.m.Keys);
  //        assert unchanged(m'.m.Values - {b});
  //        assume COK(b, m.oHeap + m.ns);
  //        assume m'.m.Values - {b} + {b} == m'.m.Values;
  // //       assert
  //        assert CallOK(m'.m.Values, m.oHeap + m.ns);
  //
  //         assert m'.calidObjects();
  //         assert m'.calidOK();
  //         assert m'.calidMap();
  //         assert m'.calidSheep();
  //
  //
  assert old(m'.calid());
  //     }

  return;
}
//end Clone_All_Fields





method Clone_Outside_Heap(a : Object, m' : Map)
  returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 //Clone_Outside_Heap

  //extraOK  requires a.extra == {} //extra not yet cloned

  //this case
  requires a !in m'.ks
  requires a !in m'.vs

  requires outside(a,m'.o)
  requires a.region.Heap?

  //all Clone_
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap) //bonus - covered in the above :-)

  ensures  m.calid()
  ensures  a == b
  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b, m.oHeap+m.ns)

  //should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
  //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
  ensures MapOK(m.m)
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
                          //this means that on return, every owner is now in the map...
  ensures a.extra <= m.ks //ditto?
  ensures m.from(m')

  //ensures b.AMFO == set x <- a.AMFO :: m.m[x]

  ensures b.fieldModes == a.fieldModes
  //  ensures b.fields.Keys == a.fields.Keys

  //  modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  // ensures  a !in m'.ks ==> b !in m'.ns  //KJX sure about this?
  modifies {}
{
  m := m';

  assert m.ks == m'.ks;
  assert a !in m.ks;
  assert a !in m.vs;

  assert m == m';
  assert m.m == m'.m;
  assert mapLEQ(m'.m,m.m);
  assert m.from(m');

  print "Clone_Outside_Heap outside owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";
  print "VARIANT COH ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

  assert CallOK(m.oHeap) by {
    reveal m.calid();
    assert m.calid();
    reveal m.calidOK();
    assert m.calidOK();
    reveal CallOK();
    assert CallOK(m.oHeap);
  }

  assert (a.Ready() && a.Valid()) by {
    reveal CallOK();
    assert CallOK(m.oHeap);
    assert a in m.oHeap;
    COKfromCallOK(a, m.oHeap);
    reveal COK();
    assert COK(a, m.oHeap);
    assert a.Ready();
    assert a.Valid();
  }


  assert a.OwnersValid() by {
    assert a.Ready();
    assert a.Valid();
    assert a.OwnersValid();
  }

  // argh OVERKILL - won't work...
  //    assert a.AMFO <= m.ks by {
  //
  //           assert COK(a, m.oHeap);
  //           reveal m.calid();
  //           assert m.calid();
  //           reveal m.calidObjects();
  //           assert m.calidObjects();
  //           reveal m.calidOK();
  //           assert m.calidOK();
  //           reveal m.Map();
  //           assert m.Map();
  //
  //           assert m.ks == m.m.Keys;
  //           assert MapOK(m.m);
  //           assert forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys;
  //    }




  assert COK(a.region.owner, m.oHeap) by {
    assert a.OwnersValid();
    assert a.AMFO > a.region.owner.AMFO;
    assert CallOK(m.oHeap);
    COKfromCallOK(a, m.oHeap);
    reveal COK();
    assert COK(a, m.oHeap);
    a.CallMyOwnersWillWitherAway(a, m.oHeap);
    assert COK(a.region.owner, m.oHeap);
  }

  assert CallOK(a.extra, m.oHeap) by {
    assert a.OwnersValid();
    assert a.extra <= a.AMFO;
    assert CallOK(m.oHeap);
    assert COK(a,m.oHeap);
    assert a.extra <= m.oHeap by {
      assert COK(a,m.oHeap);
      reveal COK();
      assert a.extra <= m.oHeap;
    }
    CallOKNarrowFocus(a.extra, m.oHeap);
    reveal CallOK();
    assert COK(a, m.oHeap);
    a.CallMyOwnersWillWitherAway(a, m.oHeap);
    assert CallOK(a.extra, m.oHeap);
  }


  //preconditions for the call..
  // assert m.calid();
  // assert a.region.owner in m.oHeap;
  assert COK(a.region.owner, m.oHeap);
  // assert outside(a.region.owner, m.o); //TEMP TO WRITEOUTSIDE CASE

  //extraOK reveal COK(); assert a.extra == {}; //extra not yet cloned

  var rowner, rm := Clone_Via_Map(a.region.owner, m);

  assert rowner in rm.vs;
  //assert rowner.AMFO <= rm.vs;  //shouild be able ot do this p- it follows
  assert a.region.owner in rm.ks;
  assert a.region.owner.AMFO <= rm.ks;

  assert a.region.owner.AMFO <= rm.ks;
  assert a.AMFO == a.region.owner.AMFO + a.extra + {a};

  assert rm.from(m);
  assert rm.from(m');
  assert MapOK(rm.m);
  reveal rm.calid(); assert rm.calid();
  reveal rm.calidObjects(); assert rm.calidObjects();
  assert rm.ks == rm.m.Keys;
  reveal rm.calidMap(); assert  rm.calidMap();
  assert (forall x <- rm.m.Keys, oo <- x.AMFO :: rm.m[oo] in rm.m[x].AMFO);
  assert (forall x <- rm.ks,     oo <- x.AMFO :: rm.m[oo] in rm.m[x].AMFO);
  assert rm.ks >= m'.ks;
  assert mapLEQ(m'.m,rm.m);
  assert rm.from(m);

///WHY THE FuCK DO I NEED TO DO THIS?
///BEST GUESS TO EnSURE ALL The OWNERS of a are in the map
///becuse it's outside it shouldn't actually CLONE ANYTHING

///BUT things hop around insidef, e.g. so we've already copied "a" in the recursive call
///can we just be done?
///Hmm. fuck I hate this shit

  //Hmm do we even need to do this?
  //or won't the recursive call handle it anyway??
  if (a in rm.ks) {
    m := rm;
    assert m.from(rm);
    reveal m.calid();
    assert m.calid();
    reveal m.calidObjects();
    assert m.calidObjects();
    reveal m.calidSheep();
    assert m.calidSheep();

    assert m.at(a).fieldModes == a.fieldModes;
    b := m.at(a);
    assert b == m.m[a];

    assert (b == a) by {
      assert not(inside(a, m.o));   //glurk
      reveal m.AreWeNotMen();
      assert m.AreWeNotMen(a,m);
      assert ((not(inside(a, m.o))) ==> (m.m[a] == a));
      assert (m.m[a] == a);
      assert (m.m[a] == m.at(a) == a);
      assert b == a;      //double glurk
    }

    assert b.fieldModes == a.fieldModes;

    reveal m.calidOK();
    assert m.calidOK();
    assert CallOK(m.vs, m.oHeap+m.ns);
    assert b in m.m.Values;
    assert m.m.Values == m.vs;
    assert b in m.vs;
    COKfromCallOK(b, m.vs, m.oHeap+m.ns);
    assert COK(b, m.oHeap+m.ns);

    assert b.fieldModes == a.fieldModes;
    assert m.from(m');
    return; //should work because Clone_Via_Map meets all the conditiosn, right???
  }  //end if a in rm.ks


  assert a !in rm.ks;
  assert a !in rm.vs by {


    assert not(inside(a,rm.o));
    assert a !in rm.m.Keys;
    assert rm.calid();
    rm.WeAreDevo();
    assert forall k <- rm.m.Keys :: rm.AreWeNotMen(k,rm);
    assert a  in rm.oHeap;
    assert a !in rm.ns;



    Map.AintNoSunshine(a, rm);
    assert a !in rm.vs; }
  assert rm.ks >= m'.ks;
  assert mapLEQ(m'.m,rm.m);
  assert rm.from(m');

  //    //maintaing MapOK
  //         assert AMFOOKRM: a.owners() <= rm.ks by {
  //             reveal rm.calid();
  //             assert rm.calid();
  //             reveal rm.calidMap();
  //             assert rm.calidMap();
  //             assert MapOK(rm.m);
  //             reveal rm.calidObjects();
  //             assert rm.calidObjects();
  //             assert (forall x <- rm.ks, oo <- x.AMFO :: oo in rm.ks);
  //             assert a.owners() <= rm.ks by {
  //                reveal COK();
  //                assert COK(a,m.oHeap);
  //                assert a.AMFO <= m.oHeap;
  // //               assert a.owners() <= rm.ks;
  //                }
  //         }5



  assert a in rm.oHeap;
  assert COK(a, rm.oHeap);
  reveal COK();
  assert a.AMFO <= rm.oHeap;
  //  assert a.owners() <= rm.ks;
  OutsidersArentMapValues(a,rm);
  assert a !in rm.vs;
  assert a !in rm.ks;
  assert not(inside(a, rm.o));

  //m := rm[a:=b];



  assert rm.calid();
  assert a in rm.oHeap;
  assert COK(a, rm.oHeap);
  assert a.extra <= rm.oHeap;

  assert CallOK(rm.oHeap) by {
    reveal rm.calid(), rm.calidOK();
    assert rm.calid();
    assert rm.calidOK();
    reveal CallOK(), COK();
    assert CallOK(rm.oHeap);
  }


  var xm := rm;
  assert xm.ks >= m'.ks;
  assert mapLEQ(m'.m,xm.m);
  assert xm.from(rm);
  assert xm.from(m');

  assert a !in xm.ks;
  assert a !in xm.vs;


  var MX := a.extra - xm.ks;
  assert MX <= a.extra;
  var xo : Object;
  var rr : Object;
  var oldmks  : set<Object>;  //dont fucking ask
  var oldmok :=  false;

  assert !oldmok;
  assert xm == rm;
  assert xm.ks >= (m'.ks);
  assert mapLEQ(m'.m,xm.m);
  assert xm.from(m');

  assert a !in xm.ks;

  while ((MX != {}) && (a !in xm.ks))
    decreases MX
    invariant MX == a.extra - xm.ks
    invariant MX <= a.extra
    invariant xm == rm
    invariant xm.calid()
    invariant rm.calid()
    invariant old(m'.calid())
    invariant xm.from(m')
    invariant MX <= xm.oHeap
    invariant CallOK(xm.oHeap)
    invariant a.AMFO - {a} <= xm.ks + MX
    invariant a.extra <= a.AMFO
    invariant oldmok ==> assigned(oldmks)
    invariant oldmok ==> (xm.ks > oldmks)
    invariant m'.oHeap == xm.oHeap
    invariant oldmok ==> ((m'.oHeap - oldmks) > (xm.oHeap - xm.ks))
    invariant xm.ks >= (m'.ks)
    invariant xm.vs >= (m'.vs)
    invariant a !in xm.ks
  {
    assert xm == rm;
    xo :| xo in MX;
    assert xo in MX;
    MX := MX - {xo};

    assert xm.calid();
    assert xo in xm.oHeap;
    COKfromCallOK(xo,xm.oHeap);
    assert COK(xo,xm.oHeap);
    assert xo !in xm.ks;


    assert oldmok ==> (m'.oHeap - oldmks) > (xm.oHeap - xm.ks);

    assert xo in a.AMFO;
    assert a.Ready();
    assert xo in a.extra;
    assert a.AMFO > xo.AMFO;


    assert (m'.oHeap) == m'.oHeap == xm.oHeap;
    assert xm.ks >= (m'.ks);
    assert xm.from(m');

    assert  mapLEQ(m'.m,xm.m) by
    { reveal xm.calid(); assert xm.calid();
      reveal xm.calidObjects(); assert xm.calidObjects();
      assert m'.ks <= xm.ks;
      assert m'.vs <= xm.vs;
      assert m'.ks == m'.m.Keys;
      assert m'.vs == m'.m.Values;
      assert xm.ks == xm.m.Keys;
      assert xm.vs == xm.m.Values;
      assert m'.m.Keys <= xm.m.Keys;
      assert m'.m.Values <= xm.m.Values;
      assert forall k <- m'.m.Keys :: k in xm.m.Keys;
      assert forall k <- m'.m.Keys :: k in xm.m.Keys && (m'.m[k] == xm.m[k]);
    }

    //
    //                   assert xm.ks >= m'.ks;
    //                 assert a !in xm.ks;
    //
    //           assert ((m'.oHeap - m'.ks)) >= (xm.oHeap - xm.ks);
    //
    // assert  ((a.AMFO)
    //   decreases to
    //         (xo.AMFO));
    //
    //         assert ((m'.oHeap - m'.ks),
    //                (a.AMFO),
    //                (a.fields.Keys),
    //                (15)
    //           decreases to
    //                xm.oHeap - xm.ks,
    //                xo.AMFO,
    //                xo.fields.Keys,
    //                20);


    rr, rm := Clone_Via_Map(xo, xm);
    assert rm.ks >= m'.ks;
    assert mapLEQ(m'.m,rm.m);
    assert rm.from(m');

    if (a in rm.ks) {
      m := rm;
      assert m.calidObjects() by {  reveal m.calid(); assert  m.calid();  }
      assert  a in m.ks by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      b := m.m[a];
      //

      assert  b in m.vs by { reveal m.calidObjects(); assert m.calidObjects();  assert b in m.m.Values; }
      assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert m.calidOK() by {  reveal m.calid(); assert  m.calid();  }
      assert  a in m.m.Keys && m.at(a) == b;
      assert  COK(b, m.oHeap+m.ns) by {
        assert b in m.vs;
        assert CallOK(m.vs, m.oHeap+m.ns) by { reveal m.calidOK(); }
        COKfromCallOK(b, m.vs, m.oHeap+m.ns);   }

      assert m.from(m');

      assert  mapLEQ(m'.m,m.m) by
      { reveal m.calidObjects(); assert m.calidObjects();
        assert m'.ks <= m.ks;
        assert mapLEQ(m'.m,m.m);
        assert m'.m.Keys <= m.m.Keys;
        assert m'.m.Values <= m.m.Values;
      }
      assert  m.ks >= m'.ks + {a} by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  m.vs >= m'.vs + {b} by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  m.o == m'.o;
      assert  m.oHeap == m'.oHeap;
      assert  m.ns >= m'.ns;
      assert MapOK(m.m);
      assert forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys;
      assert  a in m.m.Keys;
      assert forall oo <- a.AMFO :: oo in m.m.Keys;
      assert a.AMFO <= m.m.Keys;
      assert m.ks == m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert a.AMFO <= m.ks;
      assert a.extra <= m.ks;



      assert  a == b by {
        reveal m.calid();
        assert m.calidMap();
        reveal m.calidMap();
               //    assert (forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.m[x] == x)));
        assert not(inside(a,m.o));
        assert m.m[a] == a;
        assert a == b;
      }

      assert (b.fieldModes == a.fieldModes) by { assert a == b; }

      return;
    }  // if a is in ks after clone -- if it got added magically...

    assert xo in rm.ks;
    assert xm != rm;
    //    assert rr == xo;

    MX := MX - rm.ks;
    assert rm.ks > xm.ks;
    oldmks := xm.ks;
    oldmok := true;
    xm := rm;
    assert xm.ks >= m'.ks;
    assert xm.ks > oldmks;

    assert xm.from(m');


    //          MX := a.extra - rm.ks;
    assert xm == rm;
  } // end loop MX


  assert xm == rm;
  assert xm.ks >= m'.ks;
  assert a !in xm.ks;
  assert (a.AMFO - {a})<= xm.ks;
  assert a.extra <= a.AMFO;
  assert a !in a.extra;
  assert a.extra <= (a.AMFO - {a});
  assert a.extra <= (a.AMFO - {a}) <= xm.ks;
  assert a.extra <= xm.ks;

  assert xm.calid(); assert rm.calid();
  assert a.AMFO - {a} - a.extra <= rm.ks;
  //  SubsetOfKeysOfExtendedMap(a.AMFO , rm, m);
  assert a.extra <= rm.ks;
  assert a.owners() ==  a.AMFO - {a};
  assert a.AMFO == a.region.owner.AMFO + a.extra + {a};
  assert a.owners() <= rm.ks;
  assert xm.ks >= m'.ks;
  assert xm.from(m');
  assert a !in xm.ks;

  assert a !in xm.m.Keys by { assert a !in xm.ks; }
  assert COK(a,xm.oHeap);
  assert a.Ready();
  assert a.AllOwnersAreWithinThisHeap(xm.ks);
  assert a.owners() <= xm.ks;
  assert (a.AMFO - {a}) <= xm.ks;
  assert (forall oo <- (a.AMFO - {a}) :: oo in xm.m.Keys);
  //  assert (a.region.Heap? ==> xm.m[a].region.Heap?);
  assert (a.region.Heap? ==> a.region.owner in a.AMFO);
  assert (a.region.Heap? ==> a.region.owner in xm.m.Keys);
  //  assert (a.region.Heap? ==> xm.m[a.region.owner] == xm.m[a].region.owner );
  //  assert (forall oo <- a.AMFO :: xm.m[oo] in xm.m[a].AMFO);
  assert (a.region.Heap? ==> a.extra <= a.AMFO);
  assert (forall xo <- a.extra :: xo in xm.m.Keys);
  //  assert (forall xo <- a.extra :: xm.m[xo] in xm.m[a].extra) ;

  assert a !in rm.ks;
  rm.WeAreDevo();
  assert a !in rm.vs  by { Map.AintNoSunshine(a, rm); }
  m := rm.putOutside(a);
  b := m.at(a);
  assert b == a;
  assert b.fieldModes == a.fieldModes;


  assert m.at(a).fieldModes == a.fieldModes;
  b := m.at(a);
  assert b == m.m[a];

  // why wias this still here?????
  //         assert (b == a) by {
  //           assert not(inside(a, m.o));   //glurk
  //           reveal m.AreWeNotMen();
  //           assert m.AreWeNotMen(a,m);
  //           assert ((not(inside(a, m.o))) ==> (m.m[a] == a));
  //           assert (m.m[a] == a);
  //           assert (m.m[a] == m.at(a) == a);
  //           assert b == a;      //double glurk
  //         }

  assert COK(b, m.oHeap);
  COKWiderContext(b, m.oHeap, m.ns);
  assert COK(b, m.oHeap+m.ns);

  assert m.m == MappingPlusOneKeyValue(rm.m,a,b);
  assert m.calid();
  MapOKFromCalid(m);
  assert MapOK(m.m);
  assert mapLEQ(rm.m, m.m);
  assert m.from(rm);  assert m.from(m');
  //    assert a.owners() <= rm.ks by { reveal AMFOOKRM; }
  assert a.AMFO - {a} - a.extra <= rm.ks;
  //      SubsetOfKeysOfExtendedMap(a.AMFO, rm, m);
  assert a.owners() <= m.ks;
  assert a in m.ks;
  assert a.AMFO == a.owners() + {a};
  assert a.AMFO <= m.ks;

  assert b.fieldModes == a.fieldModes;

  //END outside  HEAP OBJECT
}



method Clone_Outside_World(a : Object, m' : Map)
  returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 //Clone_Outside_World

  //extraOK  requires a.extra == {} //extra not yet cloned

  //this case
  requires a !in m'.ks
  requires outside(a,m'.o)
  requires a.region.World?

  //all Clone_
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)


  ensures  m.calid()
  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b, m.oHeap+m.ns)

  //should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
  //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
  ensures MapOK(m.m)
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures a.extra <= m.ks //ditto?
  ensures m.from(m')

  //ensures b.AMFO == set x <- a.AMFO :: m.m[x]

  ensures a.fieldModes == b.fieldModes
  // ensures b.fields.Keys == a.fields.Keys
  // modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  // ensures  a !in m'.ks ==> b !in m'.ns  //KJX sure about this?
  modifies {}
{
  m := m';


  assert ANKS: a !in m.ks;

  assert COK(a,m.oHeap);
  reveal COK();
  assert a.Ready();
  assert a.AMFO == {a};

  reveal m.calid();
  assert m.calid();
  reveal m.calidOK();
  assert m.calidOK();
  reveal m.calidSheep();
  assert m.calidSheep();

  print "Clone_Via_Map world:", fmtobj(a),"\n";
  print "VARIANT COW ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";
  assert CallOK(m.oHeap);

  b := a;
  assert b.fieldModes == a.fieldModes;




  assert a !in m.ks;
  assert a in m.oHeap;
  assert m.oHeap !! m.ns by {
    reveal m.calidObjects();
    assert m.calidObjects();
    assert m.oHeap !! m.ns;
  }
  assert outside(a,m.o);
  a.CallMyOwnersWillWitherAway(a, m.oHeap);

  reveal m.calidObjects();
  assert m.calidObjects();
  assert m.ks <= m.oHeap;
  OutsidersArentMapValues(a,m);

  reveal m.calidMap();
  assert m.calidMap();
  assert MapOK(m.m);
  assert (forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys);
  assert m.m.Keys == m.ks;
  assert (forall x <- m.ks :: x.owners() <= m.ks);

  assert a !in m.vs;
  m := m.putOutside(a);   ///HOPEY?  CHANGEY?
  assert b.fieldModes == a.fieldModes;

  assert (b == a) by {
    assert not(inside(a, m.o));   //glurk
    assert m.AreWeNotMen(a,m);
    assert b == a;      //double glurk
  }

}





// {:verify false}
method Clone_KaTHUMP(a : Object, m' : Map)
  //spike method to test AMFO being "owner-closed"
  //means the clones are "owner-cooned"
  // that all the owners (and their AMFOS) are in the current objects AMFOS
  //  i.e,  forall oo <- MYOWNERS :: oo in oo.AMFO
  //  forall oo <- MYOWNERS - this? :: oo.AMFO <= this.AMFO..
  // so if .e.g a[x] == c,   then we want m[a[x]] == m[c]...
  // (please James, write a comment about what yhis method is doing]
  returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_Heap

  //this case
  requires a !in m'.ks
  requires inside(a,m'.o)
  requires a.region.Heap?

  //extraOK  requires a.extra == {} //extra not yet clone


  //all Clone_
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)

  //from clone extra owners
  ensures  m.calid() //needed to be able to call some of the below  en
  //ensures  a.AMFO <= m.ks  //seems weird but we are populating m, right...  //kathump
  ensures  a.extra <= m.ks //ditto?
  ensures  mapThruMap(a.extra, m) <= m.vs
  ensures  m.from(m')

  // ensures  a !in m'.ks ==> b !in m'.ns
  // ensures  b  in m'.ns ==> a  in m'.ks

{ //kathump

  m := Clone_Extra_Owners(a, m');
  b := a;  //OOPS!

  assert m.calid();
  reveal m.calid();
  assert m.calidObjects();
  reveal m.calidObjects();
  assert m.calidOK();
  reveal m.calidOK();
  assert m.calidMap();
  reveal m.calidMap();
  assert m.calidSheep();
  reveal m.calidSheep();
  COKfromCallOK(a, m.oHeap);
  assert COK(a, m.oHeap);
  reveal COK();
  assert a.Ready();
  assert a.region.owner in a.AMFO;
  assert COK(m.o, m.oHeap);
  assert CallOK(m.oHeap);
  COKAMFO(a, m.oHeap);
  assert CallOK(a.AMFO, m.oHeap);
  assert a.region.owner in a.AMFO;
  assert a.extra <= a.AMFO;
  CallOKNarrowFocus(a.extra, a.AMFO, m.oHeap);
  assert CallOK(a.extra, m.oHeap);
  COKfromCallOK(a.region.owner, m.oHeap);
  assert COK(a.region.owner, m.oHeap);

  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //

  assert AllTheseOwnersAreFlatOK(a.AMFO - {a});
  //  reveal AllTheseOwnersAreFlatOK();
  assert OrigBigfoot(a.AMFO - {a});

  assert (a.region.owner.AMFO + a.extra) == a.owners();
  assert OrigBigfoot(a.extra, (a.region.owner.AMFO + a.extra));
  assert OrigBigfoot(a.extra, a.owners());
  assert OrigBigfoot(a.owners());
  assert AllTheseOwnersAreFlatOK(a.owners()) by
  {
    reveal AllTheseOwnersAreFlatOK();
    assert AllTheseOwnersAreFlatOK(a.owners());
  }
  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //

  assert forall xo <- a.extra :: xo in a.owners();
  assert a.extra <= a.owners();
  assert forall xo <- a.extra :: xo.AMFO <= a.owners();
  // assert a.owners() <= m.ks;

  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //

  assert  a.extra <= m.ks;  //should beecome AMFO?
  assert  mapThruMap(a.extra, m) <= m.vs;
  assert  m.from(m');

  assert flattenAMFOs(a.extra) <= m.oHeap;
  assert flattenAMFOs(a.extra) <= m.ks;

  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //

  // assert  a !in m'.ks ==> b !in m'.ns;
  // assert  b  in m'.ns ==> a  in m'.ks;
}





// {:verify false}
method Clone_Inside_Heap(a : Object, m' : Map)
  returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_Heap

  //this case
  requires a !in m'.ks
  requires inside(a,m'.o)
  requires a.region.Heap?

  //extraOK  requires a.extra == {} //extra not yet cloned


  //all Clone_
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)

  //requires CallOK(a.extra,m'.oHeap); ///now covered by the above?

  ensures  m.calid()
  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  b in m.ns
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b, m.oHeap+m.ns)

  //on reflection, none of these make sense - or perhaps this one does?
  //  ensures  b.fields == map[]

  //should I package this up - as aw twostate or a onestate?
  //it;s about clonbamps, so clonmapLEQ or clonmapEXTENDS
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
  //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
  ensures MapOK(m.m)
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures a.extra <= m.ks //ditto?
  ensures old(m'.calid())
  ensures m.from(m')

  //ensures b.AMFO == set x <- a.AMFO :: m.m[x]

  ensures b.fieldModes == a.fieldModes
  //   ensures b.fields.Keys == a.fields.Keys

  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  //modifies (set o : Object)`fields
  // ensures a !in m'.ks ==> b !in m'.ns  //KJX sure about this?   //Cline INsinside heap
  // ensures b in m'.ns ==> a in m'.ks
  modifies {}
{ //clone inside heap
  m := m';

  assert COK(a, m.oHeap);
  assert aFLAT: AllTheseOwnersAreFlatOK(a.AMFO - {a}) by {
    reveal COK();
    reveal AllTheseOwnersAreFlatOK();
    assert COK(a, m.oHeap);
    assert AllTheseOwnersAreFlatOK(a.AMFO - {a});
    assert AllTheseOwnersAreFlatOK(a.region.owner.AMFO);
    assert (a.AMFO - {a}) == a.extra +
                             (if (a.region.Heap?) then (a.region.owner.AMFO) else {});  //yuck
    assert (a.AMFO - {a}) == (a.extra + a.region.owner.AMFO);
    assert (AllTheseOwnersAreFlatOK(a.extra,
                                    (if (a.region.Heap?) then (a.region.owner.AMFO) else {}) + a.extra)); // also YUCK
    assert (AllTheseOwnersAreFlatOK(a.extra, (a.extra + a.region.owner.AMFO)))  ;
  }
  assert m.calid();
  assert inside(a,m.o);

  assert XXm: ExtraIsExtra(a.extra,m.oHeap) by {
    reveal COK();
    assert COK(a, m.oHeap);
    assert ExtraIsExtra(a.extra, m.oHeap);
  }

  assert ANKS: a !in m.ks;
  assert COKFOURWAYS: m.calid();

  print "Clone_Inside_Heap of:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";
  print "VARIANT CIH ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";
  assert COK(a.region.owner, m.oHeap) by {
    assert m.calid();
    reveal m.calid();
    assert m.calidOK();
    reveal m.calidOK();
    COKfromCallOK(a, m.oHeap);
    assert COK(a, m.oHeap);
    reveal COK();
    assert a.Ready();
    assert a.region.owner in a.AMFO;
    assert COK(m.o, m.oHeap);
    assert CallOK(m.oHeap);
    COKAMFO(a, m.oHeap);
    assert CallOK(a.AMFO, m.oHeap);
    assert a.region.owner in a.AMFO;
    COKfromCallOK(a.region.owner, m.oHeap);
    assert COK(a.region.owner, m.oHeap);

  }

  //makde COK check for this, no need to do another level here?
  // assert forall x <- a.extra :: COK(x,m.oHeap);
  // forall x <- a.extra ensures COK(x,m.oHeap)
  // {
  //   assert true;
  // }
  //assert CallOK(a.extra,m.oHeap);

  assert (a.region.owner.AMFO < a.AMFO) by {
    assert m.calid();
    reveal m.calid();
    assert m.calidOK();
    reveal m.calidOK();
    COKfromCallOK(a, m.oHeap);
    assert COK(a, m.oHeap);
    reveal COK();
    assert a.Ready();
    assert a.AMFO > a.region.owner.AMFO;
    assert a.region.owner.AMFO <=  a.AMFO;
  }

  print "Clone_Inside_Heap ", fmtobj(a), " recursive call ", fmtobj(a.region.owner) ,"\n";


  //extraOK        reveal COK(); assert a.region.owner.extra == {}; //extra not yet cloned

  var rowner, rm := Clone_Via_Map(a.region.owner, m);
  assert rm.from(m);

  print "Clone_Inside_Heap ", fmtobj(a), " recursive call RETURNS ", fmtobj(rowner) ,"\n";


  assert COK(rowner, rm.oHeap+rm.ns);

  reveal rm.calid();
  reveal rm.calidObjects();
  reveal rm.calidOK();
  reveal rm.calidMap();
  reveal rm.calidSheep();
  assert rm.calid();
  assert rm.calidObjects();
  assert rm.calidOK();
  assert rm.calidMap();
  assert rm.calidSheep();

  assert COK(a.region.owner, rm.oHeap);
  assert CallOK(rm.oHeap);
  assert CallOK(rm.ks, rm.oHeap);
  assert CallOK(rm.vs, rm.oHeap+rm.ns);
  assert CallOK(rm.ns, rm.oHeap+rm.ns);



  //should we rename oHeap as context?

  assert COK(rm.o, rm.oHeap);
  assert CallOK(rm.oHeap);
  assert XXrm: ExtraIsExtra(a.extra,rm.oHeap)
  by {reveal XXm; }


  // COKAMFO(rowner, rm.oHeap+rm.ns);
  // assert {rowner}+rowner.AMFO == rowner.AMFO+{rowner};
  // assert CallOK({rowner}+rowner.AMFO,
  //
  // assert CallOK({rowner}+rowner.AMFO, rm.oHeap+rm.ns);


  assert CallOK(rm.oHeap); //ensured by clone
  CallOKWiderContext(rm.oHeap,rm.oHeap,rm.ns);
  assert CallOK(rm.oHeap,rm.oHeap+rm.ns);

  assert CallOK(rm.ns, rm.oHeap+rm.ns);  //ensured by clone
  CallOKWiderFocus(rm.oHeap, rm.ns, rm.oHeap+rm.ns);

  assert CallOK(rm.oHeap+rm.ns);

  assert COK(rowner, rm.oHeap+rm.ns);  //ensured by clone

///need this for later...
  assert OKR0: COK(rowner, rm.oHeap+rm.ns);
  assert OKC0: CallOK(rm.oHeap+rm.ns);


  if (a in rm.ks) {

    print "Clone_Inside_Heap ", fmtobj(a), " already cloned: abandoning ship!!\n";


    m := rm;
    b := rm.at(a);
    assert m.calid();
    assert CallOK(m.vs, m.oHeap+m.ns);
    assert b in m.m.Values;
    assert m.m.Values == m.vs;
    assert b in m.vs;
    assert (b in m.ns) by
    {
      reveal m.calid();
      assert m.calid() && m.calidObjects() && m.calidOK() && m.calidSheep();
      reveal m.calidSheep();
      reveal m.AreWeNotMen();
      assert forall x <- m.ks :: m.AreWeNotMen(x, m);
      assert b == m.m[a];
      assert a in m.ks;
      assert inside(a,m.o);
      assert m.m[a] in m.ns;
      assert b in m.ns;
    }
    assert b in m.ns;
    assert b in rm.ns;

    COKfromCallOK(b, m.vs, m.oHeap+m.ns);
    assert COK(b, m.oHeap+m.ns);
    assert COK(b, rm.oHeap+rm.ns);

    assert b.fieldModes == a.fieldModes;
    assert m.calidSheep();

    assert m.ks >= m'.ks + {a};
    assert m.vs >= m'.vs + {b};

    return;
  } // a in rm.ks - i.e. randomly done while cloning owners

  print "Clone_Inside_Heap ", fmtobj(a), " have rowner ", fmtobj(rowner) ," self not yet cloned\n";

  assert a !in rm.ks;
  assert a.region.owner in rm.ks;

  assert COK(rowner, rm.oHeap+rm.ns);
  assert CallOK(rm.oHeap+rm.ns);
  assert a.extra <= rm.oHeap by { assert COK(a, rm.oHeap); reveal COK(); }
  CallOKNarrowFocus({},rm.oHeap+rm.ns);    //WTF is this doiung?  why?
  assert CallOK({},rm.oHeap+rm.ns);        //and this one?

  print "Clone_Inside_Heap ", fmtobj(a), " about to clone any extra owners!!\n";

///need this for later...
  assert OKR1: COK(rowner, rm.oHeap+rm.ns);
  assert OKC1: CallOK(rm.oHeap+rm.ns);


  var rrm := Clone_Extra_Owners(a, rm);
  assert rrm.from(rm);

  assert CallOK(rrm.oHeap);
  assert CallOK(rrm.oHeap, rrm.oHeap);
  assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);
  CallOKWiderContext(rrm.oHeap, rrm.oHeap, rrm.ns);
  CallOKWiderFocus(rrm.oHeap, rrm.ns, rrm.oHeap+rrm.ns);
  assert OKC2: CallOK(rrm.oHeap+rrm.ns);

///need this for later...

  //COKWiderContext2(rowner, )

  COKWiderContext2(rowner, rm.oHeap+rm.ns, rrm.oHeap+rrm.ns);
  assert OKR2: COK(rowner, rrm.oHeap+rrm.ns);

  assert XXrrm: ExtraIsExtra(a.extra,rrm.oHeap)
  by {reveal XXrm; }

  assert a.extra <= rrm.ks;
  assert a.region.owner in rm.ks;
  assert a.region.owner in rrm.ks;

  if (a in rrm.ks) {

    print "Clone_Inside_Heap ", fmtobj(a), "after Clone_Extra_Oners, seems a already cloned: abandoning ship!!\n";

    m := rrm;

    b := rrm.at(a);

    assert rrm.calid();

    reveal rrm.calid();
    reveal rrm.calidObjects();
    reveal rrm.calidOK();
    reveal rrm.calidMap();
    reveal rrm.calidSheep();
    reveal rrm.AreWeNotMen();

    assert rrm.calid();
    assert rrm.calidObjects();
    assert rrm.calidOK();
    assert rrm.calidMap();
    assert rrm.calidSheep();

    assert inside(a, rrm.o);
    assert (forall x <- rrm.ks :: rrm.AreWeNotMen(x, rrm));
    assert rrm.AreWeNotMen(a,rrm);
    assert (inside(a,rrm.o)) ==> rrm.m[a] in rrm.ns;
    assert b == rrm.m[a];

    assert b in rrm.ns;
    assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);
    COKfromCallOK(b, rrm.ns, rrm.oHeap+rrm.ns);
    assert COK(b, rrm.oHeap+rrm.ns);

    return;
  }

  assert a !in rrm.ks;

  //extraOK    assert a.AMFO  <= rrm.ks <= rrm.oHeap;
  assert a.extra <= rrm.ks;
  assert rrm.ks <= rrm.oHeap;
  assert a.extra <= rrm.oHeap;


  assert ExtraIsExtra(a.extra, rrm.oHeap)
  by {reveal XXrrm; }
  assert (forall e <- a.extra :: e in e.AMFO);

  var rextra := mapThruMap(a.extra, rrm);   //REXTRA HERE

  assert rextra <= (rrm.oHeap + rrm.ns);
  assert CallOK(rextra, rrm.oHeap+rrm.ns) by {
    reveal CallOK(), COK();
    assert rrm.from(rm);
  }
  assert ExtraIsExtra(rextra, rrm.oHeap+rrm.ns) by {
    reveal XXrrm;
    reveal CallOK(), COK();

    assert CallOK(rextra, rrm.oHeap+rrm.ns);
    assert forall e <- rextra :: COK(e, rrm.oHeap+rrm.ns);
    assert (forall e <- rextra :: e in e.AMFO);
    assert (forall e <- rextra :: e.AMFO <= rrm.oHeap+rrm.ns);

    //                assert forall x <- a.extra :: imageUnderMap(x, rrm.m[x], rrm);
  }

  //extraOK assert rextra == {};

  reveal rrm.calid();
  reveal rrm.calidObjects();
  reveal rrm.calidOK();
  reveal rrm.calidMap();
  reveal rrm.calidSheep();

  assert rrm.calid();
  assert rrm.calidObjects();
  assert rrm.calidOK();
  assert rrm.calidMap();
  assert rrm.calidSheep();

  assert COK(a,rrm.oHeap);
  reveal COK();
  assert a.owners() <= rrm.oHeap;
  assert a !in rrm.ks; // by { reveal ANKS; }

  assert OKR3: COK(rowner, rrm.oHeap+rrm.ns);
  assert OKC3: CallOK(rrm.oHeap+rrm.ns);

  //preconditions for cake...
  assert COK(rowner, rrm.oHeap+rrm.ns) by { reveal OKR3, OKC3; }
  assert CallOK(rrm.oHeap+rrm.ns) by { reveal OKR3, OKC3; }
  assert CallOK(rextra, rrm.oHeap+rrm.ns);
  assert ExtraIsExtra(rextra, rrm.oHeap+rrm.ns);

  assert (a.AMFO - {a}) == a.owners();
  assert flattenAMFOs(a.AMFO - {a}) == flattenAMFOs(a.owners());

  assert a.region.owner.AMFO + a.extra + {a} == a.AMFO;
  // assert a.region.owner.AMFO + a.extra == (a.AMFO - {a}) == a.owners();
  //
  // reveal AllTheseOwnersAreFlatOK();
  //
  //        assert AllTheseOwnersAreFlatOK(a.AMFO - {a}) by { reveal aFLAT; }
  //        assert AllTheseOwnersAreFlatOK(a.region.owner.AMFO + a.extra);
  var aAMFOs := a.region.owner.AMFO + a.extra;
  //  assert AllTheseOwnersAreFlatOK(aAMFOs);https://www.youtube.com/


  assert rextra == mapThruMap(a.extra, rrm);
  //assert forall ax <- a.extra :: imageUnderMap(ax, rrm.m[ax], rrm);
  assert rowner == rrm.m[a.region.owner];
  assert a.region.owner.AMFO  <= rrm.ks;
  assert forall ao <- a.region.owner.AMFO :: rrm.m[ao] in (rrm.m[a.region.owner]).AMFO;

  //assert forall ao <- a.region.owner.AMFO :: imageUnderMap(ao, rrm.m[ao], rrm);


  assert OrigBigfoot(a.region.owner.AMFO);
  assert AllTheseOwnersAreFlatOK(a.region.owner.AMFO);



  //reveal AllTheseOwnersAreFlatOK();

  //assert rowner.AMFO ==  mapThruMap(a.region.owner.AMFO, rrm);
  //        assert AllTheseOwnersAreFlatOK(a.region.owner.AMFO + a.extra);
  //
  //        assert AllTheseOwnersAreFlatOK(rowner.AMFO);
  //
  //        assert AllTheseOwnersAreFlatOK(a.extra, a.owners());

  var amfosToBeMinusThis := rowner.AMFO+rextra; // (rowner.AMFO+{this}+rextra)-{this};

  assert forall o <- aAMFOs ::
      && o in aAMFOs
      && o.AMFO <= aAMFOs
      && rrm.m[o] in amfosToBeMinusThis
    ;

  assert forall o <- a.extra ::
      && o in aAMFOs
      && o.AMFO <= aAMFOs
      && rrm.m[o] in rextra
    ;
  assert rextra <= amfosToBeMinusThis;

  assert forall o <- a.extra, oo <- o.AMFO ::
      && oo in aAMFOs
      && rrm.m[o]  in rextra
      && rrm.m[o]  in amfosToBeMinusThis
      && rrm.m[oo] in amfosToBeMinusThis //(rowner.AMFO + rextra)
    ;
  //
  //       assert (set o <- a.extra ::  rrm.m[o]) == mapThruMap(a.extra, rrm);
  //       assert (set o <- a.extra, oo <- o.AMFO ::  rrm.m[oo])
  //          == mapThruMap((set o <- a.extra, oo <- o.AMFO :: oo), rrm);
  //
  // assert mapThruMap(aAMFOs, rrm) == amfosToBeMinusThis;

  //  assert ((set o <- a.extra, oo <- o.AMFO :: oo) + a.extra)   //tnis should not worj!!!
  //           ==  flattenAMFOs(mapThruMap(a.extra,rrm));

  reveal AllTheseOwnersAreFlatOK();
  assert AllTheseOwnersAreFlatOK(rowner.AMFO); ///this one is OK...
  assert OrigBigfoot(rowner.AMFO);

  assert ((set o <- a.extra, oo <- o.AMFO :: oo) + a.extra)
      ==  flattenAMFOs(a.extra);

  assert (a.extra) <= (a.extra+a.region.owner.AMFO);
  assert forall o <- a.extra :: o.AMFO <= (a.extra+a.region.owner.AMFO);

  assert AllTheseOwnersAreFlatOK((a.extra), (a.extra+a.region.owner.AMFO));
  assert OrigBigfoot((a.extra),  (a.extra+a.region.owner.AMFO));

  MapThruMapPreservesSubsets(a.extra, (a.extra+a.region.owner.AMFO), m);
  MapThruMapPreservesAMFO(a.extra, (a.extra+a.region.owner.AMFO), m);

  assert OrigBigfoot(mapThruMap(a.extra, m),
                     mapThruMap(a.extra+a.region.owner.AMFO, m));




  var R := rrm.m;
  assert AllMapEntriesAreUnique(R);
  assert rextra == mapThruMap(a.extra, rrm);

  assert (forall o <- a.extra, oo <- o.AMFO ::
            && ((oo in a.region.owner.AMFO) || (oo in a.extra))
            && ((R[oo] in R[a.region.owner].AMFO) || (R[oo] in rextra)));

  assert (forall o <- a.extra, oo <- o.AMFO :: (oo in a.extra) ==>  (R[oo] in rextra));
  assert (forall o <- a.extra, oo <- o.AMFO :: (oo in a.region.owner.AMFO) ==>  (R[oo] in R[a.region.owner].AMFO));

  //  assert (set o <- a.extra, oo <- o.AMFO :: R[oo]) == (set o <- a.extra, oo <- R[o].AMFO :: oo);

  assert (forall o <- a.extra, oo <- o.AMFO :: && ((R[oo] in R[a.region.owner].AMFO) || (R[oo] in rextra)));


  assert rrm.at(a.region.owner) == rowner;
  assert R[a.region.owner] == rowner;
  assert R[a.region.owner].AMFO == rowner.AMFO;

  assert MapOK(R);

  assert  (forall x <- R.Keys, oo <- x.AMFO  :: R[oo] in R[x].AMFO);
  assert  (forall x <- R.Keys, xo <- x.extra :: R[xo] in R[x].extra);

  assert a.extra <= R.Keys;
  assert a.region.owner.AMFO <= R.Keys;

  assert (forall xo <- a.extra :: R[xo] in rextra);

  //these dont work... //cos they was WRONG - hopefully fixed now
  assert (forall xo <- a.extra, oo <- xo.AMFO :: R[oo] in (rowner.AMFO + rextra));
  assert (forall xo <- a.extra, oo <- xo.AMFO :: (R[oo] in rowner.AMFO ) || (R[oo] in rextra));

  //
  //   //these dont work either
  //   assert (forall o <- a.extra, oo <- R[o].AMFO ::
  //             && ((oo in rowner.AMFO) || (oo in rextra)))
  //     ;

  //        assert (forall o <- rextra, oo <- o.AMFO ::
  //             &&
  //       ;
  //

  //assert flatAMFOs == ((set o <- a.extra, oo <- o.AMFO :: oo) + a.extra);

  assert rextra <= amfosToBeMinusThis;
  assert rowner.AMFO <= amfosToBeMinusThis;

  reveal AllTheseOwnersAreFlatOK();

  //       var R := rrm.m;
  //       assert AllMapEntriesAreUnique(R);
  //       var M := invert(R);
  //       assert AllMapEntriesAreUnique(M);
  //
  //       assert forall r <- R.Keys :: M[R[r]] == r;


  assert (rextra) <= (rowner.AMFO+rextra);
  //assert (forall o <- rextra :: o.AMFO <=  (rowner.AMFO+rextra));
  // assert (forall o <- rextra, oo <- o.AMFO :: ((oo in rowner.AMFO) || (oo in rextra)));
  // assert (forall o <- rextra :: o.AMFO <=  (rowner.AMFO+rextra));


  assert Bigfoot(rowner.AMFO);
  assert AllTheseOwnersAreFlatOK(rowner.AMFO);

  // assert Bigfoot((rextra), (rowner.AMFO+rextra));
  // assert AllTheseOwnersAreFlatOK((rextra), (rowner.AMFO+rextra));

  var context := rrm.oHeap+rrm.ns;
  assert COK(rowner, context);
  assert CallOK(context);
  assert CallOK(rextra, context) ;
  assert ExtraIsExtra(rextra, context);
  assert AllTheseOwnersAreFlatOK(rowner.AMFO);

  assert Bigfoot(rextra, rextra + rowner.AMFO);
  assert AllTheseOwnersAreFlatOK(rextra, rextra + rowner.AMFO);
  assert AllTheseOwnersAreFlatOK(rextra, rowner.AMFO + rextra);


  b := new Object.cake(a.fieldModes, rowner, rrm.oHeap+rrm.ns, "clone of " + a.nick, rextra);



  // currently ignoring REXTRA //TODO...   //extra not yet cloned
  // var rextra := set x <- a.extra :: m.m[x];
  // b := new Object.cake(a.fieldModes, rowner, rrm.oHeap+rrm.ns, "clone of " + a.nick, rextra);

  assert fresh(b);
  assert b.fieldModes == a.fieldModes;

  assert b !in rrm.oHeap;
  assert b !in rrm.m.Values;
  assert a !in rrm.m.Keys;
  assert COK(b, (rrm.oHeap+rrm.ns)+{b});
  // COKWiderContext(b, )
  // assert COK(b, {b} + rrm.oHeap+rrm.m.Values);
  assert a.region.Heap? == b.region.Heap?;


  assert b !in rrm.vs;
  assert COK(b, rrm.oHeap+rrm.ns+{b});
  assert b !in (rrm.oHeap+rrm.ns);

  assert MapOK(rrm.m);
  //assert forall kx <- a.extra :: rrm.m[kx] in b.extra;   //extra not yet cloned

  //extraOK        assert a.extra == {}; //extra not yet cloned
  assert a.owners() <= rrm.ks;

  var xm := rrm.putInside(a,b);
  assert xm.m == MappingPlusOneKeyValue(rrm.m,a,b);

  assert xm.ks >= rrm.ks + {a};
  assert xm.vs >= rrm.vs + {b};
  assert b in xm.ns;
  assert COK(b, xm.oHeap+xm.ns);

  MapOKFromCalid(xm);
  assert xm.calid();

  print "Clone_Inside_Heap map updated ", fmtobj(a), ":=", fmtobj(b) ,"\n";


  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   preconditiosn for call of Clone_All_Fields
  /////   /////    /////    /////   /////    /////    /////   /////    /////


  assert xm.calid();
  assert COK(a, xm.oHeap);
  assert COK(b, xm.oHeap+xm.ns);
  assert b.fields.Keys == {};
  assert a.fields.Keys <= a.fieldModes.Keys;
  assert a.fieldModes == b.fieldModes;
  assert a in xm.oHeap  ;
  assert a in xm.ks;
  assert b in xm.vs;
  assert b in xm.ns;
  assert (a in xm.m.Keys) && xm.m[a] == b;
  assert xm.o    in xm.oHeap;
  assert xm.ks   <= xm.oHeap;
  assert a.region.Heap? == b.region.Heap?;


///WHAT THE FUCK FUCKUY FUCK IS GOING ON FUCKY HERE
  // assert (m'.oHeap - m'.ks) >=  (xm.oHeap - xm.ks +{a});
  // assert old((a.fields.Keys)) >= (a.fields.Keys);


  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   /////    /////    /////   /////    /////    /////   /////    /////

  m := xm;

  //        m := Clone_All_Fields(a,b, xm);

  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   /////    /////    /////   /////    /////    /////   /////    /////



  assert m.ks >= xm.ks;
  assert m.vs >= xm.vs;

  assert m.ks >= m'.ks + {a};
  assert m.vs >= m'.vs + {b};

  print "Clone_Inside_Heap of ", fmtobj(a), " retuning ", fmtobj(b) ,"\n";
}











method Clone_Inside_World(a : Object, m' : Map)
  returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_World(

  //this case
  requires inside(a,m'.o)
  requires a.region.World?
  requires a !in m'.ks

  //extraOK  requires a.extra == {} //extra not yet cloned

  //all Clone_
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)


  ensures  m.calid()
  ensures  a in m.ks
  ensures  a in m.m.Keys
  ensures  b in m.vs
  ensures  b in m.m.Values
  ensures  b in m.ns
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b, m.oHeap+m.ns)

  ensures  b.fields.Keys == a.fields.Keys

  // ensures fresh(b)

  //should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.ks >= m'.ks + {a}
  ensures  m.vs >= m'.vs + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
  //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
  ensures MapOK(m.m)
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures a.extra <= m.ks //ditto?
  ensures m.from(m')

  ensures b.fieldModes == a.fieldModes
  //   ensures b.fields.Keys == a.fields.Keys
  // ensures  a !in m'.ks ==> b !in m'.ns  //KJX sure about this?
  modifies {}
{
  m := m';

  //  assert  m.ks >= m'.ks + {a};
  //  assert  m.vs >= m'.vs + {b};

  print "VARIANT CIW ", |(m'.oHeap - m'.ks)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

  assert COK(a, m.oHeap);
  assert m.calid();
  assert inside(a,m.o);
  m.DevoIsUnique();
  assert AllMapEntriesAreUnique(m.m);

  assert ANKS: a !in m.ks;
  assert COKFOURWAYS: m.calid();


  reveal m.calid();
  assert m.calid();
  reveal m.calidOK();
  assert m.calidOK();

  print "Clone_Via_Map world:", fmtobj(a),"\n";

  assert CallOK(m.oHeap);

  assert BEFORE: m.calid();

  b := new Object.frozen2(a.fieldModes, m.oHeap);

  b.nick := "clone of " + a.nick;

  assert fresh@BEFORE(b);
  assert b !in m.oHeap;
  assert b !in m.ns;
  assert unchanged@BEFORE(m.oHeap`fields, m.oHeap`fieldModes);
  assert unchanged@BEFORE(m.ns`fields, m.ns`fieldModes);

  assert m.calid();

  assert fresh(b);
  assert b !in m.oHeap + m.ns;
  assert COK(a, m.oHeap); // by { reveal COKSTART; }
  assert COK(b, m.oHeap+{b});
  COKWiderContext(b, m.oHeap+{b}, m.ns);
  assert (m.oHeap+{b})+m.ns == m.oHeap+m.ns+{b};
  assert COK(b, m.oHeap+m.ns+{b});

  assert a !in m.ks by { reveal ANKS; }  //was m.m.Keys...
  assert a !in m.m.Keys by { reveal ANKS;  reveal m.calid(); assert m.calid(); reveal m.calidObjects(); assert m.calidObjects(); }  //was m.m.Keys...

  RVfromCOK(a, m.oHeap);
  var mx := m.putInside(a,b);

  assert (mx.ks == mx.m.Keys && mx.vs == mx.m.Values)
  by {
    reveal m.putInside();
    assert mx.calid(); reveal mx.calid();
    assert mx.calidObjects(); reveal mx.calidObjects();
  }
  assert mx.m == m.m[a:=b];
  assert mx.m == MappingPlusOneKeyValue(m.m,a,b);

  assert  mx.ks >= m'.ks + {a};
  assert  mx.vs >= m'.vs + {b};

  assert COK(b, mx.oHeap+mx.ns);

  reveal mx.calidMap();
  assert mx.calid();
  reveal mx.calidMap();
  assert mx.calidMap();
  assert MapOK(mx.m);

  assert a.AMFO == {a};
  assert a.AMFO <= mx.ks;

  m := Clone_All_Fields(a,b, mx);

  assert  (m.ks >= mx.ks && m.vs >= mx.vs)
  by {
    assert m.calid();
    reveal m.calid();
    assert m.calidObjects();
    reveal m.calidObjects();
  }

  assert  m.ks >= m'.ks + {a};
  assert  m.vs >= m'.vs + {b};

}




















method Clone_Field_Map(a : Object, n : string, b : Object, m' : Map)
  returns (m : Map)
  //clone field a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases (m'.oHeap - m'.ks +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5 //Clone_Field_Map

  requires MPRIME: m'.calid()
  requires COK(a, m'.oHeap)
  requires COK(b, m'.oHeap+m'.ns)

  requires n  in a.fields.Keys
  requires n !in b.fields.Keys

  requires n  in a.fieldModes
  requires n  in b.fieldModes
  requires a.fieldModes == b.fieldModes
  requires FLDMODZ: a.fieldModes == b.fieldModes


  requires a in m'.oHeap
  requires a in m'.ks

  requires b in m'.vs
  requires b in m'.ns
  requires (a in m'.m.Keys) && m'.m[a] == b
  requires m'.o    in m'.oHeap
  requires m'.ks   <= m'.oHeap

  requires b.fieldModes == a.fieldModes

  // requires b.fieldModes[n] == Evil //evilKJX this is actually evil
  //well not *that* evil as I still must satisfy refOK

  requires forall n <- b.fields :: (n in b.fieldModes) &&
                                   AssignmentCompatible(b, b.fieldModes[n], b.fields[n])

  //consequently
  requires refOK(a, a.fields[n])
  requires a.region.Heap? == b.region.Heap?



  ensures  b.fields.Keys == old(b.fields.Keys) + {n}
  ensures  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys)
  ensures  m.calid()
  ensures  old(m'.calid())


  ensures  a in m.ks
  ensures  (a in m.m.Keys) && m.m[a] == b

  ensures  n in b.fields
  ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]

  ensures  b in m.vs

  ensures  mapLEQ(m'.m,m.m)

  ensures  CallOK(m.oHeap)
  ensures  COK(a, m.oHeap)
  ensures  COK(b, m.oHeap+m.ns)
  ensures  CallOK(m.vs, m.oHeap+m.ns)
  ensures  CallOK(m.ns, m.oHeap+m.ns)

  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns    >= m'.ns
  ensures  m.ks    >= m'.ks
  ensures  m.vs    >= m'.vs
  ensures  m.ks    <= m.oHeap


  ensures MapOK(m.m)
  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
  ensures a.extra <= m.ks //ditto?

  ensures old(m'.calid())
  ensures m.fromold(m')

  ensures a.fieldModes == b.fieldModes

  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.vs - {b})
  ensures  unchanged(m'.ks)

  //ensures  a !in m'.ks ==> b !in m'.ns  //KJX sure about this?
  //  in this case, a should be in kis, b in b',ns

  ensures  unchanged(m'.ns - {b})  //will this work?

  //  ensures unchanged(m.vs - {b}) //duesb;t veruft....

  //  modifies (set o : Object | o !in m'.oHeap)`fields
  // modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns?
  modifies b`fields
{
  assert m'.calid() by { reveal MPRIME; }
  assert unchanged(m'.ns);

  m := m';

  var v_cfm := ((m.oHeap - m.ks +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map



  print "VARIANT CFM ", |(m'.oHeap - m'.ks)+{a}|, " ", |a.AMFO|, " ", |(a.fields.Keys - b.fields.Keys - {n})|, " ", 10, "\n";

  var onb := m.ns - {b};
  var ctx := (m.oHeap+m.ns);

  assert CallOK(onb, ctx) by
  {
    assert m.calid(); reveal m.calid(); reveal m.calidOK();
    assert CallOK(m.ns, m.oHeap+m.ns);
    CallOKNarrowFocus(onb, m.ns, m.oHeap+m.ns);
    assert CallOK(onb, m.oHeap+m.ns);
  }

  assert CallOK(m.oHeap) by {
    assert m.calid(); reveal m.calid();
    assert m.calidOK(); reveal m.calidOK();
    assert CallOK(m.oHeap);
  }

  assert m.calid();
  assert old(m'.calid());

  assert unchanged(m'.ns);

  var ofv := COKat(a,n,m.oHeap);

  label B3:
  assert m.calid();
  assert m'.calid() by { reveal MPRIME; }



  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

  var rfv, rm := Clone_Via_Map(ofv, m);

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //


  //assert rfv !in m'.ns;
  assert unchanged(m'.ns);

  assert m'.calid() by { reveal MPRIME; }

  assert unchanged@B3(m.oHeap);

  assert rfv in  rm.oHeap+rm.vs;
  assert rfv in  rm.oHeap+rm.ns;
  assert COK(rfv,rm.oHeap+rm.ns);
  assert refOK(b, rfv);
  assert AssignmentCompatible(b, b.fieldModes[n], rfv)
  by {
    // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

    assert b.fieldModes[n] == a.fieldModes[n];

    assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]) by
    {
      reveal COK();
      assert COK(a, m.oHeap);
      assert a.Valid();
      assert a.AllFieldsContentsConsistentWithTheirDeclaration();
      assert forall n <- a.fields.Keys :: AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
      assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
    }





    match (b.fieldModes[n]) {
      case Evil =>
        assert b.fieldModes[n] == Evil;
        EVILisCompatibleWithAnything(b,rfv);
        assert AssignmentCompatible(b, b.fieldModes[n], rfv);

      case Rep | Owned(_) | Loaned(_) =>
        assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
        assert ofv == a.fields[n];
        assert ofv.region.Heap?;
        assert ofv.region.owner == a;
        assert rfv.region.Heap?;
        assert b == rm.m[a];
        assert rfv == rm.m[ofv];
        assert b == rfv.region.owner;
        assert b == rm.m[a.fields[n].region.owner];
        assert b == rfv.region.owner;
        assert AssignmentCompatible(b, b.fieldModes[n], rfv);

      case Peer =>
        assert AssignmentCompatible(a, a.fieldModes[n], ofv);
        assert a.region == ofv.region;
        if a.region.Heap? {
          assert b.region.Heap?;
          assert rm.m[a.region.owner] == b.region.owner;
          assert rm.m[ofv.region.owner] == rfv.region.owner;
          assert rfv.region.owner == b.region.owner;
          assert b.region.owner       == rfv.region.owner;
        } else {
          assert AssignmentCompatible(a, a.fieldModes[n], rfv);

          assert a.region.World?;
          assert b.region.World?;
        }
        assert b.region == rfv.region;
        assert AssignmentCompatible(b, b.fieldModes[n], rfv);

      case Borrow(pp,bb,nn,ff) =>
        assert refOK(a,a.fields[n]);
        assert refOK(b,rfv);
        assert AssignmentCompatible(b, b.fieldModes[n], rfv);
    }



    // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
  }




  assert rm.calid();
  assert m.calid();
  m := rm;
  assert rm.calid();
  assert m.calid();

  bNotInoHeap(b,m);

  label B4:

  assert m.calidOK() by { reveal m.calid(); }
  assert m'.calid() by { reveal MPRIME; }


  assert COK(b, rm.oHeap+rm.ns) by
  {
    assert b in m'.ns;
    assert b in m.ns;
    assert b in rm.ns;
    assert COK(b, m'.oHeap+m'.ns);
    assert m'.ns <= rm.ns <= m.ns;
    COKWiderContext2(b,m'.oHeap+m'.ns,rm.oHeap+rm.ns);
    assert COK(b, rm.oHeap+rm.ns);
  }


  assert
    && CallOK(m.vs, m.oHeap+m.ns)
    && CallOK(m.ns, m.oHeap+m.ns)
    && ( m.ks    <= m.oHeap )
  by { reveal m.calid(); reveal m.calidOK(); }

  CallOKNarrowFocus(m.vs-{b}, m.vs, m.oHeap+m.ns);
  CallOKNarrowFocus(m.ns-{b}, m.ns, m.oHeap+m.ns);

  assert CallOK(m.vs-{b}, m.oHeap+m.ns);
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);

  assert b in m.ns;

  label JUSTBEFORE:

  b.fields := b.fields[n := rfv];

  assert unchanged(m'.ns - {b});

  assert CallOK(m.vs-{b}, m.oHeap+m.ns);
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);


  assert m.m[ofv] == rfv;
  assert rfv in m.vs;
  assert rfv in m.oHeap+m.ns;


  if (b != rfv) {

    assert rm == m;

    assert COK(rfv,m.oHeap+m.ns);
    assert COK(b,  m.oHeap+m.ns) by {
      reveal COK();
      assert refOK(b, rfv);
      assert AssignmentCompatible(b, b.fieldModes[n], rfv);

      assert COK(b,  m.oHeap+m.ns);
    }

  } else {
    assert b == rfv;// gulp!

    assert COK(b,  m.oHeap+m.ns) by {
      reveal COK();
      assert refOK(b, rfv);
      assert AssignmentCompatible(b, b.fieldModes[n], rfv);
      assert COK(b,  m.oHeap+m.ns);
    }
    assert COK(rfv,m.oHeap+m.ns);
  }

  assert unchanged(m'.ns - {b});

  assert m'.calid2();
  assert old(m'.calid());

  assert COK(b, m.oHeap+m.ns) &&  COK(rfv,m.oHeap+m.ns);


  //
  assert   (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys) by {
    assert a.fields.Keys == old(a.fields.Keys);
    assert b.fields.Keys == old(b.fields.Keys)+{n};
  }


  assert
    && CallOK(m.vs, m.oHeap+m.ns)
    && CallOK(m.ns, m.oHeap+m.ns)
  by {
    assert CallOK(m.vs-{b}, m.oHeap+m.ns); //OK
    assert CallOK(m.ns-{b}, m.oHeap+m.ns);

    assert COK(b, m.oHeap+m.ns);
    assert b in  m.oHeap+m.ns by { reveal COK(); }
    CallOKfromCOK(b, m.oHeap+m.ns);
    CallOKWiderFocus(m.ns-{b}, {b}, m.oHeap+m.ns);
    assert (m.ns-{b} + {b}) == m.ns;

    assert b in m'.vs;
    assert b in  m.vs;

    assert m.vs <= m.oHeap+m.ns by { reveal m.calid(); reveal m.calidOK(); }

    assert COK(b, m.oHeap+m.ns);
    assert b in  m.oHeap+m.ns by { reveal COK(); }
    CallOKfromCOK(b, m.oHeap+m.ns);
    CallOKWiderFocus(m.vs-{b}, {b}, m.oHeap+m.ns);
    assert (m.vs-{b} + {b}) == m.vs;


    assert CallOK(m.vs, m.oHeap+m.ns);
    assert CallOK(m.ns, m.oHeap+m.ns);
  }

  //OLDCALID assert m'.calid() by { reveal MPRIME; }

  assert  m.calidOK()
  by {
    assert old@B4(rm.calidOK());
    reveal m.calidOK();

    assert old@B4(CallOK(m.vs, m.oHeap+m.ns));
    assert old@B4(CallOK(m.ns, m.oHeap+m.ns));


    assert rfv in rm.vs;
    assert rfv in rm.oHeap+rm.ns;
    assert COK(rfv,m.oHeap+m.ns);

    assert (m.o in  m.oHeap);
    assert (m.ks <= m.oHeap);
    assert (m.vs <= m.oHeap+m.ns);
    assert COK(m.o, m.oHeap);
    assert CallOK(m.oHeap);
    assert CallOK(m.ks, m.oHeap);

    assert COK(b,m.oHeap+m.ns);

    // assert CallOK(m.vs, m.oHeap+m.ns);
    // assert CallOK(m.ns, m.oHeap+m.ns);
    assert m.calidOK();
  }


  assert unchanged(m'.ns - {b});


  assert m.calid() by
  {
    reveal m.calid();
    reveal m.calidObjects();
    reveal m.calidOK();
    reveal m.calidMap();
    reveal m.calidSheep();

    assert m.calidObjects();
    assert m.calidOK();
    assert m.calidMap();

    assert m.ks == m.m.Keys;
    reveal m.AreWeNotMen();
    assert forall x <- m.ks :: m.AreWeNotMen(x, m);
    assert m.calidSheep();

    assert m.calid();

  }
  //
  //   assert m'.calid() by {
  //
  //      reveal MPRIME; reveal m'.calid();
  //
  //      assert old@JUSTBEFORE(m'.calid());
  //      assert m.calid();
  //
  //      assert n !in  old@JUSTBEFORE(b.fields.Keys);
  //
  //      assert old(m'.calid());
  //     }

  assert old(m'.calid());

} //end Clone: /_Field_Map




function mapThruMap(os: set<Object>, m : Map) : (r : set<Object>)
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
  requires m.calid()
  requires os <= m.ks
  requires os <= m.m.Keys

  ensures  r  <= m.m.Values
  ensures  r  <= m.vs <= (m.oHeap + m.ns)

{
  reveal m.calid(), m.calidOK();
  set o <- os :: m.m[o]
}

function  mapThruMappingKV(os : set<Object>, m : Mapping, k : Object, v : Object) : (r : set<Object>)
  requires os <= m.Keys + {k}

  ensures  r  <= m.Values + {v}
{
  set o <- os :: if (o == k) then (v) else (m[o])
}


lemma mapThruMappingKVIsNICE(os : set<Object>, m : Mapping, k : Object, v : Object)
  requires os <= m.Keys + {k}
  requires k !in m.Keys //technically unnecessary but nice to have?
  requires v !in m.Values //technically unnecessary but nice to have?

  ensures  (set o <- os :: if (o == k) then (v) else (m[o]))  ==  (set o <- os :: m[k:=v][o])
  ensures  m[k:=v].Keys == m.Keys+{k}
//  ensures  m[k:=v].Values == m.Values+{k}
  ensures  k in m[k:=v].Keys
  ensures  v in m[k:=v].Values
  ensures  forall x <- m.Keys :: x in m[k:=v].Keys
{
}



function  mapThruMapKV(os : set<Object>, m : Map, k : Object, v : Object) : (r : set<Object>)
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
  requires m.calid()
  requires os <= m.ks + {k}
  requires os <= m.m.Keys + {v}

  ensures  r  <= m.m.Values + {v}
  ensures  r  <= (m.vs + {v}) <= (m.oHeap + m.ns + {v})
{
  reveal m.calid(), m.calidOK();
  set o <- os :: if (o == k) then (v) else (m.m[o])
}



lemma mapThruMapPreservesLessSameMore(less: set<Object>, same: set<Object>, more : set<Object>, m : Map)
  requires m.calid()
  requires less <= m.ks
  requires less <= m.m.Keys
  requires same <= m.ks
  requires same <= m.m.Keys
  requires more <= m.ks
  requires more <= m.m.Keys
  requires less == same
  requires less <  more
  requires same <  more
  ensures  mapThruMap(less,m) == mapThruMap(same,m)
  ensures  mapThruMap(less,m) <= mapThruMap(more,m)
  ensures  mapThruMap(same,m) <= mapThruMap(more,m)
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();

  BothSidesNow(m.m);

  assert forall l <- less :: l in same;
  assert forall l <- less :: l in more;
  assert forall s <- same :: s in less;

  assert forall l <- mapThruMap(less,m) :: l in mapThruMap(same,m);
  assert forall l <- mapThruMap(less,m) :: l in mapThruMap(more,m);
  assert forall s <- mapThruMap(same,m) :: s in mapThruMap(less,m);

  assert mapThruMap(less,m) == mapThruMap(same,m) <= mapThruMap(more,m);
}


lemma MapThruMapPreservesSubsets(less: set<Object>, more : set<Object>, m : Map)
  requires m.calid()
  requires less <= m.ks
  requires less <= m.m.Keys
  requires more <= m.ks
  requires more <= m.m.Keys
  requires less <= more
  ensures  mapThruMap(less,m) <= mapThruMap(more,m)
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  BothSidesNow(m.m);

  assert forall l <- less :: l in more;

  assert forall l <- mapThruMap(less,m) :: l in mapThruMap(more,m);

  assert mapThruMap(less,m) <= mapThruMap(more,m);
}



lemma MapThruMapPreservesSets(less: set<Object>, more : set<Object>, m : Map)
  requires m.calid()
  requires less <= m.ks
  requires less <= m.m.Keys
  requires more <= m.ks
  requires more <= m.m.Keys
  requires less == more
  ensures  mapThruMap(less,m) <= mapThruMap(more,m)
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  BothSidesNow(m.m);

  MapThruMapPreservesSubsets(less, more, m);
  MapThruMapPreservesSubsets(more, less, m);

  assert mapThruMap(less,m) == mapThruMap(more,m);
}



lemma MapThruMapIsInvertible(less: set<Object>, other: set<Object>,  m : Map)
//I hate the term "injective" must be a better one. invertible?
  requires m.calid()
  requires less <= m.ks
  requires less <= m.m.Keys
  requires other == mapThruMap(less, m)
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  BothSidesNow(m.m);
  reveal UniqueMapEntry();

  //var other :=  (set x <- less :: m.m[x]);
  //var other := mapThruMap(less, m);

  var inverse := invert(m.m);

  var one := (set x <- other :: inverse[x]);

  assert forall l <- less  :: m.m[l] in other;
  assert forall o <- other :: inverse[o] in m.m;

//   assert |less| == |other| == |one|;
//
//   assert m.m.Keys == inverse.Values;
//   assert m.m.Values == inverse.Keys;

  assert one == less;
}




lemma MapThruMapSingleton(l : Object, m : Map)
  requires m.calid()
  requires {l} <= m.ks
  requires {l} <= m.m.Keys
  ensures  mapThruMap({l},m) == {m.m[l]}
{
  assert (set o <- {l} :: m.m[o]) == {m.m[l]};
}

//WUY THE FUCK CAN"T I USE SOME OF THESE!!!



lemma MapThruMapPreservesAMFO(less: set<Object>, other : set<Object>, m : Map)
  requires m.calid()
  requires less <= m.ks
  requires less <= m.m.Keys
  requires other == mapThruMap(less, m)
  //ensures  forall l <- less :: mapThruMap(l.AMFO,m) == m.m[l].AMFO
  ensures  forall l <- less :: l.AMFO <= m.ks
  ensures  forall l <- less :: (set oo <- l.AMFO :: m.m[oo]) == m.m[l].AMFO
  {
  reveal m.calid();
  assert m.calid();
  reveal m.calidOK();
  assert m.calidOK();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidMap();
  assert m.calidMap();
  reveal m.calidSheep();
  assert m.calidSheep();
  assert MapOK(m.m);

  reveal UniqueMapEntry();
  }


lemma MapThruMapKVExtendsAMFO(m : Map, k : Object, v : Object)
  requires m.calid()
  requires k !in m.ks
  requires v !in m.vs
  requires k.AMFO <= m.ks+{k}
  requires v.AMFO <= m.vs+{v}
  requires k in  m.oHeap
  requires v in  m.oHeap+m.ns
  requires mapThruMappingKV(k.AMFO, m.m, k, v) == v.AMFO

  requires
    && (k.AMFO <= m.ks+{k})
    && (k.region.Heap? == v.region.Heap?)
    && (k.region.Heap? ==> (k.region.owner in k.AMFO))
    && (k.region.Heap? ==> (k.region.owner in m.ks))
    && (k.region.Heap? ==> (m.m[k.region.owner] == v.region.owner))
    && (k.region.Heap? ==> (k.extra <= m.ks+{k}))
    && (k.region.Heap? ==> (k.extra <= k.AMFO))
    && (k.extra <= m.ks+{k})
    && (v.extra <= m.vs+{v})
    && (k.extra == v.extra)
    && (mapThruMappingKV(k.extra, m.m, k, v) == v.extra)


  ensures (
    var bb := m.m[k:=v];
    && (forall x <- bb.Keys :: x.AMFO <= bb.Keys)
    && (forall x <- bb.Keys :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO)
  )
   ///what it SHOULD BE
  // ensures  MapOK(m.m[k:=v])
{
  reveal m.calid();
  assert m.calid();
  reveal m.calidOK();
  assert m.calidOK();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidMap();
  assert m.calidMap();
  reveal m.calidSheep();
  assert m.calidSheep();
  assert MapOK(m.m);

  reveal UniqueMapEntry();

assert && (forall k <- m.m.Keys :: (set oo <- k.extra :: m.m[oo])  == m.m[k].extra);

  var aa := m.m;

assert && (forall k <- aa.Keys  :: (set oo <- k.extra :: aa[oo])   == aa[k].extra);

assert mapThruMappingKV(k.extra, m.m, k, v) == v.extra;
assert mapThruMappingKV(k.extra,  aa, k, v) == v.extra;

      assert //expanded body of MapOK!
        && (forall x <- aa.Keys :: x.AMFO <= aa.Keys)
        && (forall x <- aa.Keys :: (set oo <- x.AMFO :: aa[oo]) == aa[x].AMFO)
        && (forall x <- aa.Keys :: x.region.Heap? == aa[x].region.Heap?)
        && (forall x <- aa.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
        && (forall x <- aa.Keys |  x.region.Heap? :: x.region.owner in aa.Keys)
        && (forall x <- aa.Keys |  x.region.Heap? :: aa[x.region.owner] == aa[x].region.owner )

        && (forall x <- aa.Keys |  x.region.Heap? :: x.extra <= x.AMFO)
        && (forall x <- aa.Keys |  x.region.Heap? :: x.extra <= aa.Keys)
        && (forall x <- aa.Keys, xo <- x.extra :: xo in aa.Keys)
        && (forall x <- aa.Keys, xo <- x.extra :: aa[xo] in aa[x].extra)
        && (forall x <- aa.Keys :: (set oo <- x.extra :: aa[oo])  == aa[x].extra)
      ;

assert k.AMFO <= m.ks+{k};

assert v.AMFO == mapThruMappingKV(k.AMFO, aa, k, v);
assert v.AMFO == (set oo <- k.AMFO :: if (oo == k) then (v) else (aa[oo]));

var bb := aa[k:=v];

assert k.AMFO <= bb.Keys;
assert bb[k] == v;

assert  forall x <- aa.Keys     :: bb[x] == aa[x];
assert  forall x <- {k}         :: bb[x] == v;
assert  forall x <- aa.Keys+{k} :: bb[x] == (if (x == k) then (v) else (aa[x]));
assert  forall x <- bb.Keys     :: bb[x] == (if (x == k) then (v) else (aa[x]));

assert v.AMFO == (set oo <- k.AMFO :: if (oo == k) then (v) else (aa[oo]));

assert (forall oo <- k.AMFO      :: bb[oo] == (if (oo == k) then (v) else (aa[oo])));
assert (forall oo <- aa.Keys     :: bb[oo] == (if (oo == k) then (v) else (aa[oo])));
assert (forall oo <- aa.Keys+{k} :: bb[oo] == (if (oo == k) then (v) else (aa[oo])));
assert aa.Keys+{k} == bb.Keys;
assert (forall oo <- bb.Keys     :: bb[oo] == (if (oo == k) then (v) else (aa[oo])));

assert (forall oo <- aa.Keys  :: bb[oo] == aa[oo]);
assert bb[k] == v;

assert  (set oo <- k.AMFO :: bb[oo]) == v.AMFO by {
  assert bb[k] == v;
  assert forall b <- bb.Keys | b != k :: bb[b] == aa[b];
  assert forall oo <- bb.Keys :: bb[oo] == (if (oo == k) then (v) else (aa[oo]));

  assert mapThruMappingKV(k.AMFO, aa, k, v) == v.AMFO;
  assert (set o <- k.AMFO :: if (o == k) then (v) else (aa[o])) == v.AMFO;
  assert forall oo <- bb.Keys :: bb[oo] == (if (oo == k) then (v) else (aa[oo]));
  assert (set oo <- k.AMFO :: bb[oo]) == v.AMFO;
}

assert  (forall x <- {k} :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO);



assert  (set oo <- k.extra :: bb[oo]) == v.extra by {
  assert bb[k] == v;
  assert forall b <- bb.Keys | b != k :: bb[b] == aa[b];
  assert forall oo <- bb.Keys :: bb[oo] == (if (oo == k) then (v) else (aa[oo]));

  assert mapThruMappingKV(k.extra, aa, k, v) == v.extra;
  assert (set o <- k.extra :: if (o == k) then (v) else (aa[o])) == v.extra;
  assert (set oo <- k.extra :: bb[oo]) == v.extra;
}





    assert //expanded body of MapOK!
        && (k.extra <= m.ks+{k})
        && ((set oo <- k.extra :: bb[oo]) == v.extra)
        && (k.region.Heap? ==> (k.extra <= k.extra))
        && (k.region.Heap? ==> (k.extra <= bb.Keys))
        && (k.extra <= bb.Keys)
        && (k.extra == v.extra)
        && ((set oo <- k.extra :: bb[oo])  == v.extra)
      ;


      assert //expanded body of MapOK!
        && (forall x <- {k} :: x.AMFO <= bb.Keys)
        && (forall x <- {k} :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO)
        && (forall x <- {k} :: x.region.Heap? == bb[x].region.Heap?)
        && (forall x <- {k} |  x.region.Heap? :: x.region.owner in x.AMFO)
        && (forall x <- {k} |  x.region.Heap? :: x.region.owner in bb.Keys)
        && (forall x <- {k} |  x.region.Heap? :: bb[x.region.owner] == bb[x].region.owner )
        && (forall x <- {k} |  x.region.Heap? :: x.extra <= x.AMFO)
        && (forall x <- {k} |  x.region.Heap? :: x.extra <= bb.Keys)
        && (forall x <- {k}, xo <- x.extra :: xo in bb.Keys)
        && (forall x <- {k}, xo <- x.extra :: bb[xo] in bb[x].extra)
        && (forall x <- {k} :: (set oo <- x.extra :: bb[oo])  == bb[x].extra)
      ;

      assert (forall x <- (aa.Keys) :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO) by {
          assert (forall x <- (aa.Keys) :: (set oo <- x.AMFO :: aa[oo]) == aa[x].AMFO);
          assert (forall x <- (aa.Keys) :: bb[x] == aa[x]);
          assert (forall x <- (aa.Keys) :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO);
      }

      assert (forall x <- {k} :: x.AMFO <= bb.Keys);
      assert (forall x <- {k} :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO);

      assert (forall x <- aa.Keys :: x.AMFO <= aa.Keys);
      assert (forall x <- aa.Keys :: x.AMFO <= bb.Keys);

      assert (forall x <- aa.Keys+{k}       :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO) by {
          assert (forall x <- {k} :: x.AMFO <= bb.Keys);

          assert (forall x <- aa.Keys       :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO);
          assert (forall x <- {k}           :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO);
          assert aa.Keys + {k} == (aa.Keys+{k});
          assert aa.Keys <= (aa.Keys+{k});
          assert k in (aa.Keys+{k});
          assert (aa.Keys+{k}) <= bb.Keys;
          assert forall x <- aa.Keys       :: x in bb.Keys;
          assert forall x <- {k}           :: x in bb.Keys;
          assert forall x <- (aa.Keys+{k}) :: x in bb.Keys;
          assert (forall x <- (aa.Keys+{k}) :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO);
      }

//       assert //expanded body of MapOK!
//
//         && (forall x <- (aa.Keys) :: (set oo <- x.AMFO :: aa[oo]) == aa[x].AMFO)
//         && (forall x <- (aa.Keys) :: bb[x] == aa[x])
//         && (forall x <- (aa.Keys) :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO)
//         && (forall x <- (aa.Keys) :: x.AMFO <= bb.Keys)
//
//         && (forall x <- (aa.Keys) :: x.region.Heap? == bb[x].region.Heap?)
//         && (forall x <- (aa.Keys) |  x.region.Heap? :: x.region.owner in x.AMFO)
//         && (forall x <- (aa.Keys) |  x.region.Heap? :: x.region.owner in bb.Keys)
//         && (forall x <- (aa.Keys) |  x.region.Heap? :: aa[x.region.owner] == bb[x].region.owner )
//         && (forall x <- (aa.Keys) |  x.region.Heap? :: x.extra <= x.AMFO)
//         && (forall x <- (aa.Keys) |  x.region.Heap? :: x.extra <= bb.Keys)
//         && (forall x <- (aa.Keys), xo <- x.extra :: xo in bb.Keys)
//         && (forall x <- (aa.Keys), xo <- x.extra :: aa[xo] in bb[x].extra)
//         && (forall x <- (aa.Keys) :: (set oo <- x.extra :: aa[oo])  == bb[x].extra)
//       ;


      // assert //expanded body of MapOK!
      //   && (forall x <- (aa.Keys+{k}) :: x.AMFO <= bb.Keys)
      //   && (forall x <- (aa.Keys+{k}) :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO)
      //   && (forall x <- (aa.Keys+{k}) :: x.region.Heap? == bb[x].region.Heap?)
      //   && (forall x <- (aa.Keys+{k}) |  x.region.Heap? :: x.region.owner in x.AMFO)
      //   && (forall x <- (aa.Keys+{k}) |  x.region.Heap? :: x.region.owner in bb.Keys)
      //   && (forall x <- (aa.Keys+{k}) |  x.region.Heap? :: aa[x.region.owner] == bb[x].region.owner )
      //   && (forall x <- (aa.Keys+{k}) |  x.region.Heap? :: x.extra <= x.AMFO)
      //   && (forall x <- (aa.Keys+{k}) |  x.region.Heap? :: x.extra <= bb.Keys)
      //   && (forall x <- (aa.Keys+{k}), xo <- x.extra :: xo in bb.Keys)
      //   && (forall x <- (aa.Keys+{k}), xo <- x.extra :: aa[xo] in bb[x].extra)
      //   && (forall x <- (aa.Keys+{k}) :: (set oo <- x.extra :: aa[oo])  == bb[x].extra)
      // ;


//       assert //expanded body of MapOK!
//         && (forall x <- bb.Keys :: x.AMFO <= bb.Keys)
//         && (forall x <- bb.Keys :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO)
//         && (forall x <- bb.Keys :: x.region.Heap? == bb[x].region.Heap?)
//         && (forall x <- bb.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
//         && (forall x <- bb.Keys |  x.region.Heap? :: x.region.owner in bb.Keys)
//         && (forall x <- bb.Keys |  x.region.Heap? :: bb[x.region.owner] == bb[x].region.owner )
//
//         && (forall x <- bb.Keys |  x.region.Heap? :: x.extra <= x.AMFO)
//         && (forall x <- bb.Keys |  x.region.Heap? :: x.extra <= bb.Keys)
//         && (forall x <- bb.Keys, xo <- x.extra :: xo in bb.Keys)
//         && (forall x <- bb.Keys, xo <- x.extra :: bb[xo] in bb[x].extra)
//         && (forall x <- bb.Keys :: (set oo <- x.extra :: bb[oo])  == bb[x].extra)
//       ;


// assert v.AMFO == (set oo <- k.AMFO :: bb[oo]);

//    assert MapOK(m.m[k:=v]);
//
//    assert MapOK(bb);
}


lemma {:verify false} SHITTYMapThruMapPreservesAMFO(less: set<Object>, more : set<Object>, m : Map)
  ensures  forall l <- less, la <- l.AMFO :: la in more
  ensures  forall l <- less, la <- mapThruMap(l.AMFO,m) :: la in mapThruMap(more,m)
  ensures  forall l <- less :: mapThruMap(l.AMFO,m) <= mapThruMap(more,m)

  // ensures  forall r <- mapThruMap(less,m) :: r.AMFO <= mapThruMap(more,m)
{
  reveal m.calid();
  assert m.calid();
  reveal m.calidOK();
  assert m.calidOK();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidMap();
  assert m.calidMap();
  reveal m.calidSheep();
  assert m.calidSheep();
  assert MapOK(m.m);

  reveal UniqueMapEntry();

  BothSidesNow(m.m);

  forall l <- less
    ensures mapThruMap(l.AMFO, m) <= mapThruMap(more, m)
  {
    assert l.AMFO <= more;
    MapThruMapPreservesSubsets(l.AMFO, more, m);
    assert mapThruMap(l.AMFO, m) <= mapThruMap(more, m);
  }
}

//
// lemma HowFuckedIsThat(less: set<Object>, m : Map, i : Mapping)
//   requires i == invert(m.m)
//   requires m.calid()
//   requires less <= m.ks
//   requires less <= m.m.Keys
//   requires (forall l <- less, oo <- l.AMFO :: oo in less)
//   ensures  (forall l <- less :: l.AMFO <= less)
//   ensures  (forall l <- less, oo <- l.AMFO :: m.m[oo] in m.m[l].AMFO)
//   ensures  (forall i <- less, j <- less :: (m.m[i] == m.m[j]) <==> (i == j))
//   // ensures  (forall l <- less, j <- m.m[l].AMFO ::
//   //                  exists i <- l.AMFO :: m.m[i] == j)\
//   requires AllMapEntriesAreUnique(m.m)
//   ensures (forall l <- less, q <- m.m[l].AMFO :: ((q in i.Keys) && (i[q] in l.AMFO))))
// //
// //   ensures forall l <- less, la <- l.AMFO :: la in more
//   // ensures forall l <- less, la <- mapThruMap(l.AMFO,m) :: la in mapThruMap(more,m)
//   // ensures forall l <- less :: mapThruMap(l.AMFO,m) <= mapThruMap(more,m)
//
// // ensures  forall r <- mapThruMap(less,m) :: r.AMFO <= mapThruMap(more,m)
// {
//     reveal m.calid();
//     assert m.calid();
//     reveal m.calidOK();
//     assert m.calidOK();
//     reveal m.calidObjects();
//     assert m.calidObjects();
//     reveal m.calidMap();
//     assert m.calidMap();
//     reveal m.calidSheep();
//     assert m.calidSheep();
//     assert MapOK(m.m);
//
//     reveal UniqueMapEntry();
//
//     BothSidesNow(m.m);
// }

lemma HowReallyReallyFuckedIsThat(o : Object, m : Map, i : Mapping)
  requires AllMapEntriesAreUnique(m.m)
  requires i == invert(m.m)
  requires m.calid()
  requires o in m.ks
  requires o in  m.m.Keys
  requires o.AMFO <= m.ks
  requires o in  m.m.Keys
  // requires o.owners() <= m.ks  //need to update - all my owners EXCEPT ME!
  // requires o.owners() <= m.m.Keys

{
  reveal m.calid();
  assert m.calid();
  reveal m.calidOK();
  assert m.calidOK();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidMap();
  assert m.calidMap();
  reveal m.calidSheep();
  assert m.calidSheep();
  assert MapOK(m.m);
  reveal UniqueMapEntry();
  BothSidesNow(m.m);

  assert CallOK(m.ks, m.oHeap);
  CallOKNarrowFocus({o}, m.ks, m.oHeap);
  assert CallOK({o}, m.oHeap);
  COKfromCallOK(o, {o}, m.oHeap);
  assert COK(o, m.oHeap);
  reveal COK();
  assert AllTheseOwnersAreFlatOK(o.AMFO - {o});


  var p := m.m[o];
  assert i[p] == o;
  BothSidesNow(i);
  reveal UniqueMapEntry();
  var MAMFO := mapThruMap(o.AMFO, m);
  assert forall q <- mapThruMap(o.AMFO,m) :: q in i.Keys;
  assert forall q <- MAMFO  :: q in i.Keys;
  assert MAMFO <= i.Keys;
  assert forall k <- m.m.Keys :: m.m[k] in i.Keys;
  assert m.m.Keys == i.Values;
  assert m.m.Values == i.Keys;

  assert forall k <- m.m.Keys :: i[ m.m[k] ] == k;

  assert forall k <- m.m.Keys :: k.AMFO <= m.m.Keys;

  assert o.AMFO <= m.m.Keys;
  assert MAMFO  <= i.Keys;
  assert p == m.m[o];
  assert (forall x <- m.m.Keys, oo <- x.AMFO :: m.m[oo] in m.m[x].AMFO);
  assert forall oo <- o.AMFO :: m.m[oo] in m.m[o].AMFO;
  assert forall oo <- o.AMFO :: m.m[oo] in MAMFO;
  assert forall oo <- MAMFO  :: i[oo]   in o.AMFO;

  assert forall oo <- o.AMFO :: m.m[oo]  in p.AMFO;
  assert (set oo <- o.AMFO   :: m.m[oo]) <= p.AMFO;

  // assert (forall x <- m.m.Keys ::
  //        (set oo <- x.AMFO :: m.m[oo]) == m.m[x].AMFO);
  // assert (set oo <- o.AMFO :: m.m[oo]) == p.AMFO;


  assert forall oo <- o.AMFO :: i[ m.m[oo] ] in o.AMFO;
  assert (set oo <- o.AMFO   :: i[ m.m[oo] ]) == o.AMFO;
  assert (set oo <- o.AMFO   ::    m.m[oo]  ) == MAMFO;


  //  assert forall oo <- p.AMFO :: i[oo] in o.AMFO;

  // assert (set oo <- MAMFO :: i[oo]) == o.AMFO;
  // assert (set oo <- p.AMFO :: i[oo]) == o.AMFO;


  //     assert p.AMFO <= i.Keys;
  //
  //     assert MAMFO == p.AMFO;

  assert forall q <- o.AMFO :: m.m[q] in p.AMFO;

  assert forall q <- p.AMFO :: (q in i.Keys);   //X


  //    assert forall q <- p.AMFO :: (q in i.Keys) && (i[q] in o.AMFO);

}


// incomplete, albeit a nice idea.
// probably need to put more stuff into calidSheep to make clear its a sheep :-)
// potentially even ANOTHER invariant because not all maps are full images?
//
// lemma MapThruMapIsImage(m : Map)
//  requires m.calid()
// // ensures forall o <- m.ks :: imageUnderMap(o, m.m[o], m)
//  {
//   reveal m.calid();
//   reveal m.calidObjects();
//   reveal m.calidOK();
//   reveal m.calidMap();
//   reveal m.calidSheep();
//
//   assert forall a <- m.ks ::
//     var b := m.m[a];
//       && ((a in m.ks) && (b == m.m[a]))
//       && (a.region.Heap? == b.region.Heap?)
//       && (a.region.Heap? ==> ((a.region.owner in m.ks) && (b.region.owner == m.m[a.region.owner])))
//       && (a.extra <= m.ks)
//       // && (b.extra == mapThruMap(a.extra, m))
//       // && (a.fieldNames() == b.fieldNames())
//       // && (a.outgoing() <= m.ks)
//       // && (forall n <- a.fieldNames() :: b.fields[n]  == m.m[a.fields[n]])
//       ;
//
//  }

predicate imageUnderMap(a : Object, b : Object, m : Map)
  reads a, b
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
  requires m.calid()
{
  reveal m.calid();
  reveal m.calidObjects();
  reveal m.calidOK();
  reveal m.calidMap();
  reveal m.calidSheep();

  && ((a in m.ks) && (b == m.m[a]))
  && (a.region.Heap? == b.region.Heap?)
  && (a.region.Heap? ==> ((a.region.owner in m.ks) && (b.region.owner == m.m[a.region.owner])))
  && (a.extra <= m.ks)
  && (b.extra == mapThruMap(a.extra, m))
  && (a.fieldNames() == b.fieldNames())
  && (a.outgoing() <= m.ks)
  && (forall n <- a.fieldNames() :: b.fields[n]  == m.m[a.fields[n]])
}


method Clone_Extra_Owners(a : Object,  m' : Map)  returns (m : Map)

  decreases (m'.oHeap - m'.ks), a.AMFO, (a.fields.Keys), 12

  requires a !in m'.ks //mustn't have cloned a yet...
  requires COK(a, m'.oHeap)
  requires m'.calid()

  ensures  m.calid()
  //ensures  a !in m.ks //mustn't have cloned a yet...
  ensures  a.extra <= m.ks  //should beecome AMFO? - oh yep
  //  ensures  a.AMFO <= m.ks  //should beecome AMFO? - oh yep

  ensures  mapThruMap(a.extra, m) <= m.vs
  //  ensures  mapThruMap(a.AMFO, m) <= m.vs

  ensures  m.from(m')

  modifies {}
  //TODO  ensures a.AMFO <= m.ks  //seems weird but we are populating m, right...
{
  var rm := m';
  var b : Object;  //do we care..

  assert rm.from(m');
  reveal rm.calid(),   rm.calidObjects(),   rm.calidOK(),   rm.calidMap(),   rm.calidSheep();
  assert rm.calid() && rm.calidObjects() && rm.calidOK() && rm.calidMap() && rm.calidSheep();

  assert a in rm.oHeap;
  assert COK(a, rm.oHeap);
  reveal COK();
  assert a.AMFO <= rm.oHeap;

  assert forall x <- a.AMFO :: inside(a,x);

  // if (outside(a,rm.o)) {
  //   OutsidersArentMapValues(a,rm);
  //   assert a !in rm.vs;
  //   assert a !in rm.ks;
  //   assert not(inside(a, rm.o));
  // }


  assert CallOK(rm.oHeap) by {
    reveal rm.calid(), rm.calidOK();
    assert rm.calid();
    assert rm.calidOK();
    reveal CallOK(), COK();
    assert CallOK(rm.oHeap);
  }


  var xm := rm;
  assert xm.ks >= m'.ks;
  assert mapLEQ(m'.m,xm.m);
  assert xm.from(rm);
  assert xm.from(m');

  assert forall x <- a.AMFO  :: inside(a,x);
  assert forall x <- a.extra :: inside(a,x);

  var MX := a.extra - xm.ks;
  assert MX <= a.extra;
  assert forall x <- MX :: inside(a,x);

  var xo : Object;
  var rr : Object;
  var oldmks  : set<Object>;  //dont fucking ask
  var oldmok :=  false;

  assert !oldmok;
  assert xm == rm;
  assert xm.ks >= (m'.ks);
  assert mapLEQ(m'.m,xm.m);
  assert xm.from(m');


  while ((MX != {}) && (a !in xm.ks))
    decreases MX
    invariant MX == a.extra - xm.ks
    invariant MX <= a.extra
    invariant forall x <- MX :: inside(a,x)
    invariant xm == rm
    invariant xm.calid()
    invariant rm.calid()
    invariant old(m'.calid())
    invariant xm.from(m')
    invariant MX <= xm.oHeap
    invariant CallOK(xm.oHeap)
    invariant a.extra - {a} <= xm.ks + MX //this one?
    invariant a.extra <= a.AMFO
    invariant oldmok ==> assigned(oldmks)
    invariant oldmok ==> (xm.ks > oldmks)
    invariant m'.oHeap == xm.oHeap
    invariant oldmok ==> ((m'.oHeap - oldmks) > (xm.oHeap - xm.ks))
    invariant xm.ks >= (m'.ks)
    invariant xm.vs >= (m'.vs)
  {
    assert xm == rm;
    xo :| xo in MX;
    assert xo in MX;
    assert inside(a,xo);

    MX := MX - {xo};

    assert xm.calid();
    assert xo in xm.oHeap;
    COKfromCallOK(xo,xm.oHeap);
    assert COK(xo,xm.oHeap);
    assert xo !in xm.ks;


    assert oldmok ==> (m'.oHeap - oldmks) > (xm.oHeap - xm.ks);

    assert xo in a.AMFO;
    assert a.Ready();
    assert xo in a.extra;
    assert a.AMFO > xo.AMFO;


    assert (m'.oHeap) == m'.oHeap == xm.oHeap;
    assert xm.ks >= (m'.ks);
    assert xm.from(m');

    assert  mapLEQ(m'.m,xm.m) by
    {
      reveal xm.calid(); assert xm.calid();
      reveal xm.calidObjects(); assert xm.calidObjects();
      assert m'.ks <= xm.ks;
      assert m'.vs <= xm.vs;
      assert m'.ks == m'.m.Keys;
      assert m'.vs == m'.m.Values;
      assert xm.ks == xm.m.Keys;
      assert xm.vs == xm.m.Values;
      assert m'.m.Keys <= xm.m.Keys;
      assert m'.m.Values <= xm.m.Values;
      assert forall k <- m'.m.Keys :: k in xm.m.Keys;
      assert forall k <- m'.m.Keys :: k in xm.m.Keys && (m'.m[k] == xm.m[k]);
    }


    assert xm.ks >= m'.ks;
    assert a !in xm.ks;

    assert ((m'.oHeap - m'.ks)) >= (xm.oHeap - xm.ks);

    assert ((a.AMFO) decreases to (xo.AMFO));

    assert ((m'.oHeap - m'.ks),
            (a.AMFO),
            (a.fields.Keys),
            (15)
            decreases to
            xm.oHeap - xm.ks,
            xo.AMFO,
            xo.fields.Keys,
            20);

    assert inside(a, xo);


    rr, rm := Clone_Via_Map(xo, xm);

    assert rm.ks >= m'.ks;
    assert mapLEQ(m'.m,rm.m);
    assert rm.from(m');

    if (a in rm.ks) {
      m := rm;
      assert m.calidObjects() by {  reveal m.calid(); assert  m.calid();  }
      assert  a in m.ks by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      b := m.m[a];
      //

      assert  b in m.vs by { reveal m.calidObjects(); assert m.calidObjects();  assert b in m.m.Values; }
      assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert m.calidOK() by {  reveal m.calid(); assert  m.calid();  }
      assert  a in m.m.Keys && m.at(a) == b;
      assert  COK(b, m.oHeap+m.ns) by {
        assert b in m.vs;
        assert CallOK(m.vs, m.oHeap+m.ns) by { reveal m.calidOK(); }
        COKfromCallOK(b, m.vs, m.oHeap+m.ns);   }

      assert m.from(m');
      assert  mapLEQ(m'.m,m.m) by
      { reveal m.calidObjects(); assert m.calidObjects();
        assert m'.ks <= m.ks;
        assert mapLEQ(m'.m,m.m);
        assert m'.m.Keys <= m.m.Keys;
        assert m'.m.Values <= m.m.Values;
      }
      assert  m.ks >= m'.ks + {a} by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  m.vs >= m'.vs + {b} by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  m.o == m'.o;
      assert  m.oHeap == m'.oHeap;
      assert  m.ns >= m'.ns;
      assert MapOK(m.m);
      assert forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys;
      assert  a in m.m.Keys;
      assert forall oo <- a.AMFO :: oo in m.m.Keys;
      assert a.AMFO <= m.m.Keys;
      assert m.ks == m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert a.AMFO <= m.ks;
      assert a.extra <= m.ks;

      assert (b.fieldModes == a.fieldModes);

      return;
    }  // if a is in ks after clone -- if it got added magically...

    assert xo in rm.ks;
    assert xm != rm;

    MX := MX - rm.ks;
    assert rm.ks > xm.ks;
    oldmks := xm.ks;
    oldmok := true;
    xm := rm;
    assert xm.ks >= m'.ks;
    assert xm.ks > oldmks;

    assert xm.from(m');

    assert xm == rm;
  } // end loop MX

  m := xm;
}










lemma MapOKFromCalid(m : Map)
  requires m.calid()
  ensures  MapOK(m.m)
{  ////
  reveal m.calid();
  reveal m.calidMap();
}



lemma  OutsidersArentMapValues(a : Object, m : Map)
  requires m.calid()
  requires a in m.oHeap  //technically redundant
  requires COK(a, m.oHeap)
  requires outside(a,m.o) //TEMP TO WRITEOUTSIDE CASE
  requires a !in m.ks
  ensures  a !in m.vs
{
  reveal m.calid();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidSheep();
  assert m.calidSheep();
  reveal m.AreWeNotMen();

  assert m.ns !! m.oHeap;
  assert forall x <- m.ks :: m.AreWeNotMen(x, m);

  assert
    && (forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.m[x] == x)))
    && (forall x <- m.ks ::    ((inside(x,m.o)) ==> (m.m[x] in m.ns)))
    ;

  if (a in m.vs) {
    AValueNeedsAKey(a,m.m);

    assert {:contradiction} not(outside(a,m.o));
    assert {:contradiction} false;
  }
}




lemma {:onlyClone} OwnersValidFromCalid(a : Object, m : Map)
  requires m.calid()
  requires
    || COK(a, m.oHeap)
    || (CallOK(m.oHeap) && (a in m.oHeap))
    || (CallOK(m.ks, m.oHeap) && (a in m.ks))
    || (CallOK(m.ks, m.oHeap+m.ns) && (a in m.ks))
    || (CallOK(m.ks, m.oHeap+m.ns) && (a in m.ks))
  ensures a.Ready()
  ensures a.OwnersValid()
{
  reveal m.calid();
  assert m.calid();
  reveal m.calidOK();
  reveal COK();
  reveal CallOK();
  assert
    || (COK(a, m.oHeap) && a.Ready())
    || (CallOK(m.oHeap) && (a in m.oHeap) && a.Ready())
    || (CallOK(m.ks, m.oHeap) && (a in m.ks) && a.Ready())
    || (CallOK(m.ks, m.oHeap+m.ns) && (a in m.ks) && a.Ready())
    || (CallOK(m.ks, m.oHeap+m.ns) && (a in m.ks) && a.Ready());

  assert a.Ready();
  assert a.OwnersValid();
}
















///aux lemmas etc

lemma  bNotInoHeap(b : Object, m : Map)
  // auxilliary lemma that says ensures that b is not in oHeap :-)
  requires b in m.ns
  requires m.calid()
  ensures  b in (set o : Object | o !in m.oHeap)
{

  assert b in (set o : Object | o !in m.oHeap) by {
    assert m.calid(); reveal m.calid();
    assert m.calidObjects(); reveal m.calidObjects();
    assert m.ns !! m.oHeap;
    assert b  in m.ns;
    assert b !in m.oHeap;
    assert b  in (set o : Object | o !in m.oHeap);
  }
}


predicate {:onlyfans} isIsomorphicMappingOWNED(a : Object, o : Object, m : Mapping, os : set<Object>)
  //is a a clone of o via m within os
  decreases os
  reads os + m.Keys + m.Values
{
  && (a in m)  && (
       || (a == m[a])   //make it  easy on ourselves?
       || (
            //   && ({a,o} <= os)
            && (a in m)
            && (
                 var b := m[a];
                 && (b in os)
                 && (|| (a.region.World? && b.region.World?)
                     || (&& (a.region.Heap? && b.region.Heap?)
                         && isIsomorphicMappingOWNED(a.region.owner, b.region.owner, m, os - {a,b}))
                    )
                 && forall n <- a.fields.Keys :: (
                                                   && (a.fields[n] in m)
                                                   && (n in b.fields)
                                                   && (b.fields[n] == m[a.fields[n]])
                                                   && (isIsomorphicMappingOWNED(a.fields[n], o, m, os - {a,b}))
                                                 )
               )
          )
     )
}


























































/////     /////     /////     /////     /////     /////     /////
    /////     /////     /////     /////     /////     /////     /////
/////     /////     /////     /////     /////     /////     /////
    /////     /////     /////     /////     /////     /////     /////



datatype Klon = Klon
(
  m : iso<Object,Object>,  //m : Mapping
  ks : set<Object>, //ks - set, keys of the mapping   (must be m.Keys, subset of oHeap)
  vs : set<Object>, //vs - set, values or the mapping (must be m.Values, subset of oHeap + ns)
  o : Object,  //o - Owner within which the clone is being performaed, in oHeap
  //    p : Object,  // Owner of the new (target) clone.  needs to be inside the source object's movement
  oHeap : set<Object>,  //oHeap - original (sub)heap contianing the object being cloned and all owners and parts
  ns : set<Object> //ns - new objects  (must be !! oHeap,   vs <= oHeap + ns
  )
{
}

function klonKV(c' : Klon, k : Object, v : Object) : (c : Klon)
  requires klonIsoOK(c'.m)
  requires canKlonKV(c', k, v)
  ensures  klonIsoOK(c.m)
{

   c'.(m:= isoKV(c'.m,k,v))
}


predicate canKlonKV(c' : Klon, k : Object, v : Object)
{
  && canIsoKV(c'.m, k, v)
  && (k.AMFO <= c'.m.Keys+{k})
  && (mapThruIsoKV(k.AMFO, c'.m, k, v) == v.AMFO)
}

predicate klonIsoOK(m : iso<Object,Object>)
{
//AMFO
  && (forall k <- m.Keys :: k.AMFO <= m.Keys)
  && (forall k <- m.Keys :: (set oo <- k.AMFO :: m[oo]) == m[k].AMFO)

//region & owners?
  // && (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?)
  // && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
  // && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys)
  // && (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner )

//extra>
//   && (forall x <- m.Keys |  x.region.Heap? :: x.extra <= x.AMFO)
//   && (forall x <- m.Keys |  x.region.Heap? :: x.extra <= m.Keys)
//   && (forall x <- m.Keys, xo <- x.extra :: xo in m.Keys)
//   && (forall x <- m.Keys, xo <- x.extra :: m[xo] in m[x].extra)
//   && (forall k <- m.Keys :: (set oo <- k.extra :: m[oo])  == m[k].extra)
}

