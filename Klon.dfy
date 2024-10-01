//future refactoring TODOs
// oHeap -> contest
// o -> pivot
// o -> ?? nuOwner
// shoiuld klon(c') functions become fgunctiosn on Klon?

function klonKV(c' : Klon, k : Object, v : Object) : (c : Klon)
//extends klon mapping with k:=v
  requires klonVMapOK(c'.m)
  requires klonCanKV(c', k, v)
  ensures  klonVMapOK(c.m)
{
   var c := c'.(m:= VMapKV(c'.m,k,v));
   c
}

predicate klonCanKV(c' : Klon, k : Object, v : Object)
//extending c' with k:=v will be klonVMapOK
{
  && canVMapKV(c'.m, k, v)
  && (k.AMFO <= c'.m.Keys+{k}) 
  && (mapThruVMapKV(k.AMFO, c'.m, k, v) == v.AMFO)

  && (k.owner <= k.AMFO)
  && (k.owner <= c'.m.Keys+{k})  
  && (mapThruVMapKV(k.owner, c'.m, k, v) == v.owner)
}

predicate klonVMapOK(m : vmap<Object,Object>, ks : set<Object> := m.Keys)
//klonVMapOK the vmap parts of a klon are OK
//still need to do something for iHeap and ns etc
{
//AMFO  
  && (forall k <- m.Keys :: k.AMFO <= m.Keys)
  && (forall k <- m.Keys :: mapThruVMap(k.AMFO, m) == m[k].AMFO)

//region & owners?
  && (forall x <- m.Keys :: x.owner <= x.AMFO)
  && (forall x <- m.Keys :: x.owner <= m.Keys)
  && (forall x <- m.Keys :: mapThruVMap(x.owner, m) == m[x].owner)

//field values? //KJX
} 



datatype Klon = Klon
(
  m : vmap<Object,Object>, // maps from Original to Clone (or non-clone)
//  m.Keys : set<Object>, //m.Keys - set, keys of the mapping   (must be m.Keys, subset of oHeap)
//  m.Values : set<Object>, //m.Values - set, values or the mapping (must be m.Values, subset of oHeap + ns)
  o : Object,  //o - Owner within which the clone is being performaed, in oHeap  // "pivot"
  //    p : Object,  // Owner of the new (target) clone.  needs to be inside the source object's movement
  oHeap : set<Object>,  //oHeap - original (sub)heap contianing the object being cloned and all owners and parts
  ns : set<Object> //ns - new objects  (must be !! oHeap,   m.Values <= oHeap + ns
  )
{

  predicate from(prev : Klon)
    // should this be unique or not?
    // m.from(prev) assuming prev.klonVMapOK, then I',m Klon(OK) and a a "strict but improper extension"
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
    && o     == prev.o
    && oHeap == prev.oHeap
    && ns    >= prev.ns
  }


  static lemma fromityH(a : Object, context : set<Object>, prev : Klon, next: Klon)
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
    reads m.Values, m.Keys, o, oHeap
  {
    &&  unchanged(m.Values - except)
    &&  unchanged(m.Keys - except)
    &&  unchanged({o} - except)
    &&  unchanged(oHeap - except)
  }




  opaque function at(k : Object) : (v : Object)
    //return value corresponding to key k
    //k must be in the map
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calid()
    requires k in m.Keys
    //requires reveal calid(); reveal calidObjects();  m.Keys == m.Keys
    //requires k in m.Keys
    ensures  k in m.Keys
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
    requires AllTheseOwnersAreFlatOK({k})
  {
    reveal CallOK(), COK();
    assert k.Ready();

    var jd := new Object.make( map[], {k}, {k}, "hello");
    assert jd !in oHeap;
    Vance(jd);
  }

  method Vance(v : Object)
    requires v !in oHeap
  {}



  lemma habeusKeyus(k : Object, v : Object)
    requires calid()
    //requires v in m.Values
    requires (k in m.Keys) ==> (m[k] == v)

    // requires  k in m.Keys
    // requires  k in m.Keys //to guard the next one

    // ensures  v  in ns ==> k  in m.Keys
    // ensures  k !in m.Keys ==> v !in ns
    ensures  (v !in ns) && (v in m.Values) ==> v in oHeap

  {
    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    reveal calidMap();
    assert calidMap();
    assert klonVMapOK(m);
    assert ns <= m.Values;

    if (v in ns) {
      assert v in m.Values;
      assert gotV(v);
      assert AllMapEntriesAreUnique(m);
      AValueNeedsAKey(v, m);
    } else {
      assert  v !in ns;

    }
  }


lemma roundTrip1(k : Object, v : Object, m : Klon)
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
    assert klonVMapOK(m.m);
    assert AllMapEntriesAreUnique(m.m);

    // reveal atV();
    // reveal at();
    // reveal UniqueMapEntry();

    assert m.at(k)  == v;  //why is this needed?
    assert m.m[k]   == v;
    assert forall i <- m.m.Keys :: UniqueMapEntry(m.m, i);
    assert k in m.m.Keys;
    assert UniqueMapEntry(m.m, k);
    assert m.atV(v) == k;
  }

  static lemma roundTrip2(k : Object, v : Object, m : Klon)
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
    assert klonVMapOK(m.m);
    assert AllMapEntriesAreUnique(m.m);
  }

  opaque ghost function atV(v : Object) : (k : Object)
    //return key corresponding to value v
    //v must be in the map
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calid()
    requires v in m.Values
    //requires reveal calid(); reveal calidObjects();  m.Keys == m.Keys
    //requires k in m.Keys
    ensures  k in m.Keys
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
    ensures  g == (k in m.Keys)
    ensures  g == (k in m.Keys)  //DO I WANT THIS?
  {
    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    k in m.Keys
  }


  opaque predicate gotV(v : Object) : (g : bool)
    //is v a value in the map?
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calid()
    ensures  g == (v in m.Values)
    ensures  g == (v in m.Values)  //DO I WANT THIS?
  {
    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    v in m.Values
  }


  opaque function putInside(k : Object, v : Object) : (r : Klon)
    //put k -> v into map, k inside o
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes,  v`fields, v`fieldModes
    requires calid()
    requires k  in oHeap
    requires k !in m.Keys
    requires k !in m.Keys
    requires v !in oHeap
    requires v !in ns
    requires v !in m.Values
    requires v !in m.Values
    requires COK(k, oHeap)
    requires COK(v, oHeap+ns+{v})
    requires m.Keys <= oHeap
    requires k.allExternalOwners() <= m.Keys  //need to update - all my owners EXCEPT ME!
    requires k.allExternalOwners() <= m.Keys
    requires v.allExternalOwners() <= oHeap+ns //need to hae proceessed all owners first
    // requires v in (oHeap + ns) // should be a SEPERATIJG COJUNCTION (Below)
    // requires ((v in oHeap) != (v in ns))  //NOPE for now put it in ns
    requires (k.owner <= m.Keys) && (mapThruKlon(k.owner, this) == v.owner)
    requires forall ko <- k.allExternalOwners() :: ko in m.Keys
    requires forall ko <- k.allExternalOwners() :: m[ko] in v.AMFO
    //    requires mapThruKlon(k.allExternalOwners(), this) == (v.AMFO - {v})
    requires ((set oo <- k.allExternalOwners() :: m[oo]) == v.allExternalOwners())
    requires mapThruKlonKV(k.AMFO, this, k, v) == v.AMFO

    //      requires (k.owner <= m && m[k.owner] == v.owner)
    //      requires reveal calid(); (calid() && k.region.Heap?) ==> (got(k.owner) && (at(k.owner) == v.owner))
    //requires fresh(v)
    requires inside(k, o)
    requires v.fieldModes == k.fieldModes

    ensures  r == Klon(m[k:=v], o, oHeap, ns+{v})
    ensures  r.m.Keys == r.m.Keys
    ensures  r.m.Values == r.m.Values
    ensures  v in r.ns
    ensures  k in r.m.Keys && r.m[k] == v
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

    assert m.Keys == m.Keys;
    assert calidMap();
    reveal calidMap();
    assert calidSheep();
    reveal calidSheep();

    assert klonVMapOK(m);
    assert CallOK(oHeap);
    assert COK(k, oHeap);
    assert COK(v, oHeap+ns+{v});

    reveal COK();

    assert AllMapEntriesAreUnique(m);



    reveal calid(); assert calid();
    var rv := Klon(m[k:=v], o, oHeap, ns+{v});

    reveal calidMap(); assert calidMap(); assert klonVMapOK(m);

    assert klonKV(this,k,v).m == m[k:=v] by { reveal calidMap(); assert calidMap(); assert klonVMapOK(m);}
    assert rv == klonKV(this,k,v);

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

      assert rv.m.Keys == rv.m.Keys;
      assert rv.m.Values == rv.m.Values;
      assert rv.o in rv.oHeap;
      assert rv.m.Keys <= rv.oHeap;
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
      assert rv.m.Values <= rv.ns + oHeap;

      assert rv.calidObjects();
    }

    assert v !in m.Values; // from reqs
    assert m.Values == m.Values by {
      assert calid();
      reveal calid();
      assert calidObjects();
      reveal calidObjects();
      assert m.Values == m.Values;
    }
    assert v !in m.Values;

    assert rv.calidOK() by {
      reveal rv.calidOK();
      reveal rv.calidObjects();
      assert COK(rv.o, rv.oHeap);
      assert CallOK(rv.oHeap);
      CallOKfromCOK(k, oHeap);
      assert CallOK(m.Keys, oHeap);
      CallOKtoSubset(m.Keys, oHeap);
      CallOKWiderFocus(m.Keys, {k}, oHeap);
      assert CallOK(rv.m.Keys, rv.oHeap);
      assert oHeap+ns+{v} == rv.oHeap+rv.ns;
      assert COK(v, rv.oHeap+rv.ns);
      // CallOKWiderContext({v}, rv.oHeap, rv.ns);    //unneeded?
      // CallOKtoSubset(rv.m.Values, rv.oHeap+rv.ns);       //unneeded?
      assert rv.m.Values <= rv.ns + oHeap;
      assert CallOK(m.Values, oHeap+ns);
      CallOKWiderContext(m.Values, oHeap+ns, {v});
      assert COK(v,oHeap+ns+{v}); //reqs
      CallOKfromCOK(v, oHeap+ns+{v});   //could subsume within COK?> (or not0)
      CallOKWiderFocus(m.Values, {v}, oHeap+ns+{v});  //version just adding one?
      assert m.Values+{v} == rv.m.Values;
      assert CallOK(rv.m.Values, rv.oHeap+rv.ns);
      assert ns+{v} == rv.ns;
      CallOKWiderContext(ns,oHeap+ns,{v});  //is it worth cobinging these also
      CallOKWiderFocus(ns,{v},oHeap+ns+{v});
      assert CallOK(rv.ns, rv.oHeap+rv.ns);
      reveal rv.calidOK(); assert rv.calidOK();
    }


    // reveal rv.calidMap();
    // assert rv.calidMap() by {
    reveal rv.calidMap();
    assert klonVMapOK(rv.m) by {
      assert klonVMapOK(m);
      assert COK(k, oHeap);
      reveal COK();
      assert rv.m.Keys == m.Keys + {k};
      assert rv.m.Keys == m.Keys + {k};

      reveal rv.calidObjects();
      assert rv.calidObjects();
      reveal calidObjects();
      assert calidObjects();
      reveal calidMap();
      assert calidMap();

      assert rv.m.Keys == rv.m.Keys;
      assert k.allExternalOwners() <= m.Keys;

      assert forall x <- m.Keys :: x.AMFO <= m.Keys by {
        assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys;
      }
      assert k.allExternalOwners() <= m.Keys;
      //  assert forall x <- m.Keys+{k} :: x.owner() <= m.Keys;
      assert forall x <- m.Keys+{k} :: x.AMFO <= m.Keys+{k};
      assert (m.Keys+{k}) == m.Keys+{k} == rv.m.Keys == rv.m.Keys;
      assert forall x <- rv.m.Keys :: x.AMFO <= rv.m.Keys;
      assert forall x <- rv.m.Keys, oo <- x.AMFO :: oo in rv.m.Keys;


      assert (forall x <- rv.m.Keys  :: x.owner <= x.AMFO);
      assert (forall x <- rv.m.Keys  :: x.owner <= rv.m.Keys);
      assert (forall x <- rv.m.Keys  :: mapThruKlon(x.owner, rv) == rv.m[x].owner );

      // //BEGIN DUNNO ABOUT THIS
      //       assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);
      //       assert (forall x <- m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
      //       assert rv.m[k] == v;
      //       assert m.Keys == m.Keys;
      //       assert (k.allExternalOwners() <= m.Keys);
      //       assert (k.AMFO - {k}) <= m.Keys;
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
      assert rv == klonKV(this,k,v);


      assert mapThruKlonKV(k.AMFO, this, k, v) == v.AMFO;

      assert (forall x <- m.Keys :: (set oo <- x.AMFO :: m[oo]) == m[x].AMFO); //NEW BIT
      assert (forall x <- rv.m.Keys :: (set oo <- x.AMFO :: rv.m[oo]) == rv.m[x].AMFO);

      assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);

      //      assert (forall x <- rv.m.Keys, xo <- x.extra :: rv.m[xo] in rv.m[x].extra);

      //       assert mapThruKlon(k.allExternalOwners(), this) == (v.AMFO - {v});
      //       assert mapThruKlon(k.allExternalOwners(), this) == (v.allExternalOwners());
      //  //   assert mapThruKlon(k.AMFO, this) == (v.AMFO);//doesn't work cos k not in this.m.Keys
      //       assert ((set oo <- (k.AMFO - {k}) :: m[oo]) == v.AMFO - {v});
      //       assert ((set oo <- (k.allExternalOwners()) :: m[oo]) == v.allExternalOwners());
      // //    assert (forall x <- {k}     :: (set oo <- x.allExternalOwners() :: m[oo]) == m[x].allExternalOwners());  //dpoesn't work cos K NOT IN M yet
      //       assert (forall x <- {k}     :: (set oo <- x.allExternalOwners() :: m[oo]) == v.allExternalOwners());  //does work tho' K NOT IN M yet
      // 
      //       assert (forall x <- m.Keys     :: (set oo <- x.AMFO ::       m[oo]) == m[x].AMFO);
      //       assert (forall x <- m.Keys     :: mapThruKlon(x.AMFO, this)          == m[x].AMFO);
      //  
      //       assert (forall x <- m.Keys + {k}
      //               :: (set oo <- x.AMFO :: if (oo == k) then (v) else (m[oo]))
      //                                    == if (x  == k) then (v.AMFO) else (m[x].AMFO));
      //   
      // //    assert (forall x <- m.Keys + {k} :: mapThuMap(x.AMFO, this) == if x in m.Keys then (m[x].AMFO) else (v.AMFO)); //again k not in this & mapThru needs calid
      //       
      //       assert k !in m.Keys;
      // //      var n := m[k:=v];
      // assert k.allExternalOwners() <= m.Keys;
      //       var n := klonKV(m,k,v);
      //       MapKVOK(m,k,v,n);
      //       assert n.Keys == m.Keys + {k};
      //       assert (forall x <- m.Keys :: x in n.Keys);
      //       assert (forall x <- (m.Keys * n.Keys) :: (m[x] == n[x]));
      // 
      //       assert (forall x <- n.Keys     :: (set oo <- x.AMFO ::       n[oo]) == n[x].AMFO);
      // 
      // //    assert (forall x <- m.Keys+{k} :: (set oo <- x.AMFO :: m[k:=v][oo]) == m[k:=v][x].AMFO);
      // //    assert (forall x <- rv.m.Keys  :: mapThruKlon(x.AMFO, rv)            == rv.m[x].AMFO); //OOPS mapThruKlon needs calid...
      //       assert (forall x <- rv.m.Keys  :: (set oo <- x.AMFO ::    rv.m[oo]) == rv.m[x].AMFO);


    }  //klonVMapOK



    reveal rv.calidObjects();
    assert m.Keys == m.Keys;
    assert rv.m.Keys == rv.m.Keys;

    assert (inside(k,rv.o)) ==> (rv.m[k] in ns);
    assert rv.m[k] == v;
    assert v in ns;
    assert inside(k,rv.o);

    assert (forall x <- m.Keys  :: (not(inside(x,o)) ==> (m[x] == x)));
    assert (forall x <- m.Keys  :: (not(inside(x,o)) ==> (rv.m[x] == x)));
    assert (forall x <- {k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
    assert (forall x <- m.Keys+{k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
    assert rv.m.Keys == m.Keys + {k};
    assert rv.m.Keys == rv.m.Keys;
    assert (forall x <- rv.m.Keys  :: (not(inside(x,o)) ==> (rv.m[x] == x)));

    assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
    assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);

    reveal rv.calidMap();

    reveal UniqueMapEntry();

    assert AllMapEntriesAreUnique(m);
    assert forall i <- m.Keys :: UniqueMapEntry(m, i);
    assert k !in m.Keys;
    assert v !in m.Values;
    assert forall i <- m.Keys :: i != k;
    assert forall i <- m.Keys :: m[i] != v;
    assert forall i <- m.Keys+{k} :: (rv.m[i] == v ) ==> (k == i);
    assert forall i <- rv.m.Keys :: UniqueMapEntry(rv.m, i);

    assert
      && AllMapEntriesAreUnique(rv.m)
      && klonVMapOK(rv.m) // potentiall should expand this out?
      && (forall x <- rv.m.Keys :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)))
      && (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO)
      ;

    assert rv.calidMap();

    reveal rv.calidSheep();
    reveal rv.calidObjects();
    assert m.Keys == m.Keys;
    assert rv.m.Keys == rv.m.Keys;
    assert inside(k, o);
    reveal calidMap();
    assert calidMap();
    reveal calidSheep();


    assert forall x <- m.Keys :: AreWeNotMen(x, this);
    assert rv.m.Keys == rv.m.Keys == (m.Keys+{k});

    assert forall x <- m.Keys :: x.fieldModes == m[x].fieldModes;
    assert k.fieldModes == v.fieldModes;
    assert forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes;

    assert calidSheep();
    reveal rv.calidSheep();
    //reveal UniqueMapEntry();

    assert m.Keys == m.Keys;

    reveal AreWeNotMen();
    reveal UniqueMapEntry();
    assert forall x <- m.Keys  :: AreWeNotMen(x, this);
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
  //   ensures  forall k <- m.Keys ::
  // {
  //   reveal calid();
  //   )
  // 

  opaque function {:isolate_assertions} putOutside(k : Object) : (r : Klon)
    //put k -> k into map, k oustide o
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calid()
    requires k !in m.Keys
    requires k !in m.Values
    requires k !in m.Keys
    requires k !in m.Values
    requires k in oHeap
    requires COK(k, oHeap)
    requires k.allExternalOwners() <= m.Keys
    requires not(inside(k, o))

    requires
      && k !in m.Keys && k !in m.Values
      && COK(k,oHeap)
      && k.Ready()
      && k.AllOwnersAreWithinThisHeap(m.Keys)
      && (forall oo <- k.AMFO - {k}:: oo in m.Keys)
         //  && (m[k].region.Heap?)  WHATR THE FUCK k at in the map!
      && (k.owner <= k.AMFO)
      && (k.owner <= m.Keys)
         // && (m[k.owner] == m[k].owner )
         //  && (forall oo <- k.AMFO :: m[oo] in m[k].AMFO)
    // && (forall xo <- k.extra :: m[xo] in m[k].extra)


    ensures r == Klon(m[k:=k], o, oHeap, ns)
    ensures k in r.m.Keys && r.m[k] == k
    ensures k in r.m.Keys
    ensures k in r.m.Values
    ensures klonVMapOK(r.m)
    ensures weirdo() && (r == klonKV(this,k,k))
    ensures mapLEQ(m, r.m)
    ensures r.calid()
    ensures r.from(this)
  {

    assert  //the below should be a predicate (from klonKV)
      && k !in m.Keys
      && k !in m.Values
         //&& COK(k,m.Keys)
      && (forall oo <- k.AMFO - {k} :: oo in m.Keys)
         //&& (m[k].region.Heap?)
      && (k.owner <= k.AMFO)
      && (k.owner <= m.Keys)
         //&& (m[k.owner] == m[k].owner )
         //&& (forall oo <- k.AMFO :: m[oo] in m[k].AMFO)

         //&& (forall xo <- k.extra :: m[xo] in m[k].extra)
      ;

    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    reveal calidOK();
    assert calidOK();

    assert m.Keys == m.Keys;
    assert calidMap();
    reveal calidMap();
    assert calidSheep();
    reveal calidSheep();

    assert klonVMapOK(m);
    assert CallOK(oHeap);

    assert AllMapEntriesAreUnique(m);

    var numap := klonKV(this,k,k).m;
    assert klonVMapOK(numap);

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


    var rv := Klon(numap, o, oHeap, ns);

    assert rv == Klon(m[k:=k], o, oHeap, ns);
    assert k in rv.m.Keys && rv.m[k] == k;
    assert k in rv.m.Keys;
    assert k in rv.m.Values;
    assert klonVMapOK(rv.m);
    assert weirdo() && (rv == klonKV(this,k,k));
    assert mapLEQ(m, rv.m);


    assert rv.calidObjects() by {
      assert
        && m.Keys == m.Keys
        && m.Values == m.Values
        && o in oHeap
        && m.Keys <= oHeap
        && ns !! oHeap

        && m.Values <= ns + oHeap
        ;
    }


    assert rv.calidOK() by {
      assert (rv.o in rv.oHeap);
      assert (rv.m.Keys <= rv.oHeap);
      assert (rv.m.Values <= rv.oHeap+ns);
      assert COK(rv.o, rv.oHeap) by { assert COK(o,oHeap);  assert rv.oHeap == oHeap; assert rv.o == o; }
      assert CallOK(rv.oHeap)    by { assert CallOK(oHeap); assert rv.oHeap == oHeap; }
      assert CallOK(rv.m.Keys, rv.oHeap) by { assert CallOK(m.Keys, oHeap);
                                          assert COK(k,oHeap);
                                          CallOKfromCOK(k,oHeap);
                                          CallOKWiderFocus(m.Keys,{k},oHeap);
                                          assert rv.oHeap == oHeap;
                                          assert rv.m.Keys == m.Keys+{k}; }
      assert CallOK(rv.m.Values, rv.oHeap+rv.ns) by { assert CallOK(m.Values, oHeap+ns);
                                                assert COK(k,oHeap);
                                                CallOKfromCOK(k,oHeap);
                                                CallOKWiderContext({k},oHeap,ns);
                                                CallOKWiderFocus(m.Values,{k},oHeap+ns);
                                                assert rv.oHeap+rv.ns == oHeap+ns;
                                                assert rv.m.Values == m.Values+{k}; }
      assert CallOK(rv.ns, rv.oHeap+rv.ns) by { assert CallOK(ns, oHeap+ns);
                                                assert rv.oHeap == oHeap;
                                                assert rv.ns == ns; }
      assert rv.calidOK();
    }

    reveal rv.calidMap();
    assert rv.calidMap() by {
      reveal calidObjects(); assert calidObjects();
      reveal calidOK(); assert calidOK();
      assert klonVMapOK(m);
      assert k in rv.m.Keys;
      assert rv.m[k] == k;
      assert (forall x <- {k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
      assert (forall x <- {k}, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
      assert klonVMapOK(rv.m);

    }
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    reveal rv.calidSheep();
    assert rv.m.Keys == rv.m.Keys;
    reveal AreWeNotMen();
    assert (forall x <- rv.m.Keys :: AreWeNotMen(x, rv));
    assert (forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes);
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

  //     opaque function {:isolate_assertions} putIO(k : Object, v : Object := k) : (r : Klon)
  //       //put k -> v into map, k inside o
  //       reads oHeap`fields, oHeap`fieldModes
  //       reads ns`fields, ns`fieldModes,  v`fields, v`fieldModes
  // 
  //       requires calid()
  //       requires k  in oHeap
  //       requires k !in m.Keys
  //       requires v  in oHeap+ns+nu(k,v)
  //       requires v !in m.Values
  //       requires COK(k, oHeap)
  //       requires COK(v, oHeap+ns+nu(k,v))
  //       requires m.Keys <= oHeap
  //       requires k.allExternalOwners() <= m.Keys //hmm
  //       requires forall kx <- k.extra :: kx in m.Keys
  //       requires forall kx <- k.extra :: m[kx] in v.extra
  //       requires v.fieldModes == k.fieldModes
  // 
  //       requires if (k==v) then (v in oHeap) else (v !in oHeap)
  // 
  //       ensures  r == Klon(m[k:=v], m.Keys+{k}, m.Values+{v}, o, oHeap, ns+nu(k,v))
  //       ensures  k in r.m.Keys && r.m[k] == v
  //       ensures  COK(v, r.oHeap+r.ns)
  //       ensures  r.calid()   ///FIXFIXFIX
  //       ensures  r.from(this)
  // {
  //         var nukv := nu(k,v);
  //         var nv := ns+(nukv);
  //         var rv := Klon(m[k:=v], m.Keys+{k}, m.Values+{v}, o, oHeap, nv);
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
  //             && m.Keys == m.Keys
  //             && m.Values == m.Values
  //             && o in oHeap
  //             && m.Keys <= oHeap
  //             && ns !! oHeap
  // 
  //             && m.Values <= ns + oHeap
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
  //             assert rv.m.Keys == rv.m.Keys;
  //             assert rv.m.Values == rv.m.Values;
  //             assert rv.o in rv.oHeap;
  //             assert rv.m.Keys <= rv.oHeap;
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
  //             assert rv.m.Values <= rv.ns + oHeap;
  // 
  //             assert rv.calidObjects();
  //           }
  // 
  //           assert v !in m.Values; // from reqs
  //           assert m.Values == m.Values by {
  //             assert calid();
  //             reveal calid();
  //             assert calidObjects();
  //             reveal calidObjects();
  //             assert m.Values == m.Values;
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
  //             assert CallOK(m.Keys, oHeap);
  //             CallOKtoSubset(m.Keys, oHeap);
  //             CallOKWiderFocus(m.Keys, {k}, oHeap);
  //             assert CallOK(rv.m.Keys, rv.oHeap);
  //             assert oHeap+ns+{v} == rv.oHeap+rv.ns;
  //             assert COK(v, rv.oHeap+rv.ns);
  //             // CallOKWiderContext({v}, rv.oHeap, rv.ns);    //unneeded?
  //             // CallOKtoSubset(rv.m.Values, rv.oHeap+rv.ns);       //unneeded?
  //             assert rv.m.Values <= rv.ns + oHeap;
  //             assert CallOK(m.Values, oHeap+ns);
  //             CallOKWiderContext(m.Values, oHeap+ns, nukv);
  //             assert COK(v,oHeap+ns+nukv); //reqs
  //             CallOKfromCOK(v, oHeap+ns+nukv);   //could subsume within COK?> (or not0)
  //             CallOKWiderFocus(m.Values, {v}, oHeap+ns+{v});  //version just adding one?
  //             assert m.Values+{v}== rv.m.Values;
  //             assert CallOK(rv.m.Values, rv.oHeap+rv.ns);
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
  //             assert klonVMapOK(rv.m) by {
  //                 assert calid();
  //                 reveal calid();
  //                 assert calidObjects();
  //                 reveal calidObjects();
  //                 reveal calidMap();
  //                 assert calidMap();
  //                 assert klonVMapOK(m);
  //                 assert COK(k, oHeap);
  //                 reveal COK();
  //                 assert rv.m.Keys == m.Keys + {k};
  //                 assert rv.m.Keys == m.Keys + {k};
  // 
  //                 reveal rv.calidObjects();
  //                 assert rv.calidObjects();
  // 
  // 
  // 
  //                 assert rv.m.Keys == rv.m.Keys;
  //                 assert k.allExternalOwners() <= m.Keys;
  // 
  //                 assert forall x <- m.Keys :: x.AMFO <= m.Keys by {
  //                   assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys;
  //                 }
  //                 assert k.allExternalOwners() <= m.Keys;
  //               //  assert forall x <- m.Keys+{k} :: x.owner() <= m.Keys;
  //                 assert forall x <- m.Keys+{k} :: x.AMFO <= m.Keys+{k};
  //                 assert (m.Keys+{k}) == m.Keys+{k} == rv.m.Keys == rv.m.Keys;
  //                 assert forall x <- rv.m.Keys :: x.AMFO <= rv.m.Keys;
  //                 assert forall x <- rv.m.Keys, oo <- x.AMFO :: oo in rv.m.Keys;
  // 
  //                 assert (forall x <- rv.m.Keys :: x.region.Heap? == rv.m[x].region.Heap?);
  //                 assert (forall x <- rv.m.Keys :: x.owner <= x.AMFO);
  //                 assert (forall x <- rv.m.Keys :: x.owner <= rv.m.Keys);
  //                 assert (forall x <- rv.m.Keys :: rv.m[x.owner] == rv.m[x].owner );
  // 
  //               assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);
  //               assert (forall x <- m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
  //               assert rv.m[k] == v;
  //               assert m.Keys == m.Keys;
  //               assert (k.allExternalOwners() <= m.Keys);
  //               assert (k.AMFO - {k}) <= m.Keys;
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
  //                 assert (forall x <- rv.m.Keys :: x.extra <= x.AMFO);
  //                 assert (forall x <- rv.m.Keys :: x.extra <= rv.m.Keys);
  //                 assert (forall x <- rv.m.Keys, xo <- x.extra :: xo in rv.m.Keys);
  //                 assert (forall x <- rv.m.Keys, xo <- x.extra :: rv.m[xo] in rv.m[x].extra);
  //             }  //MAapOK
  // 
  // 
  //         
  //             reveal rv.calidObjects();
  //             assert m.Keys == m.Keys;
  //             assert rv.m.Keys == rv.m.Keys;
  //             assert (forall x <- rv.m.Keys :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
  //             assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
  //             assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);
  //             reveal rv.calidMap();
  //             assert rv.calidMap();
  // 
  //                 reveal rv.calidSheep();
  //                 reveal rv.calidObjects();
  //                 assert m.Keys == m.Keys;
  //                 assert rv.m.Keys == rv.m.Keys;
  //             assert inside(k, o);
  //             reveal calidMap();
  //             assert calidMap();
  //             reveal calidSheep();
  // 
  //             
  //             assert forall x <- m.Keys :: AreWeNotMen(x, this);
  //             assert rv.m.Keys == rv.m.Keys == (m.Keys+{k});
  // 
  //             assert forall x <- m.Keys :: x.fieldModes == m[x].fieldModes;
  //             assert k.fieldModes == v.fieldModes;
  //             assert forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes;
  // 
  //             assert calidSheep();
  //             reveal rv.calidSheep();
  //             //reveal UniqueMapEntry();
  // 
  //             assert m.Keys == m.Keys;
  // 
  //                 reveal AreWeNotMen();
  //                 reveal UniqueMapEntry();
  //             assert forall x <- m.Keys  :: AreWeNotMen(x, this);
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
    ensures  klonVMapOK(m)
    ensures  AllMapEntriesAreUnique(m)
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
  {
    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    assert m.Keys == m.Keys;
    reveal calidMap();
    assert calidMap();
    assert klonVMapOK(m);
    DevoIsUnique();
    assert AllMapEntriesAreUnique(m);
    klonVMapOK(m) &&  AllMapEntriesAreUnique(m)
  }



  opaque predicate {:onlyNUKE} AreWeNotMen(x : Object,  rv : Klon)  //hmmm wgt etc?
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





  static lemma AintNoSunshine(x : Object, rv : Klon)
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
//    reveal AreWeNotMen();
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

    ensures r ==> (m.Keys == m.Keys)
    ensures r ==> (m.Values == m.Values)
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
    && m.Keys == m.Keys
    && m.Values == m.Values

    && o in oHeap
    && m.Keys <= oHeap
    && ns !! oHeap

    && m.Values <= ns + oHeap

    && ns <= m.Values
       //&& ns == m.Values + oHeap //or is this wshat I mean?
  }

  opaque predicate  {:onlyReadFrames} calidOK()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
  {
    && (o in oHeap)
    && (m.Keys <= oHeap)
    && (m.Values <= oHeap+ns)
    && COK(o, oHeap)
    && CallOK(oHeap)
    && CallOK(m.Keys, oHeap)
    && CallOK(m.Values, oHeap+ns)
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
    && klonVMapOK(m) // potentiall should expand this out?
    && (forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x)))
    && (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO)
  }

  opaque predicate  {:onlyNUKE} calidSheep2()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calidObjects() && calidOK() && calidMap()
  {
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    reveal calidMap(); assert calidMap();
    assert m.Keys == m.Keys;

    && (forall x <- m.Keys ::
          if (inside(x,o))
          then ((m[x] in ns) && (UniqueMapEntry(m,x)))
          else ((m[x] == x)  && (UniqueMapEntry(m,x))))
    && (forall x <- m.Keys :: x.fieldModes == m[x].fieldModes)
  }


  opaque predicate {:onlyNuke} calidSheep()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calidObjects() && calidOK()// && calidMap()
  {
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    //reveal calidMap(); assert calidMap();
    assert m.Keys == m.Keys;

    reveal AreWeNotMen();
    //reveal UniqueMapEntry();

    && (forall x <- m.Keys :: AreWeNotMen(x, this))
    && (forall x <- m.Keys :: x.fieldModes == m[x].fieldModes)
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
    assert m.Keys == m.Keys;

    && (forall x <- m.Keys |    (inside(x,o)) :: (m[x] in ns))
    && (forall x <- m.Keys |    (inside(x,o)) :: (UniqueMapEntry(m,x)))
    && (forall x <- m.Keys | not(inside(x,o)) :: (m[x] == x))
    && (forall x <- m.Keys | not(inside(x,o)) :: (UniqueMapEntry(m,x)))
    && (forall x <- m.Keys :: x.fieldModes == m[x].fieldModes)
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

    assert forall x <- m.Keys ::
        if (inside(x,o))
        then ((m[x] in ns) && (UniqueMapEntry(m,x)))
        else ((m[x] == x))//  && (UniqueMapEntry(m,x)))
      ;

    reveal AreWeNotMen();
    assert forall x <- m.Keys :: AreWeNotMen(x, this);

    assert forall x <- m.Keys :: x.fieldModes == m[x].fieldModes;

  }

} ///end datatype Klon



lemma SubsetOfKeysOfExtendedMap(subset : set<Object>, left : Klon, right : Klon)
  requires left.calid()
  requires right.calid()
  requires subset <= left.m.Keys
  requires mapLEQ(left.m, right.m)
  ensures  subset <= right.m.Keys
{
  reveal Klon.calid();
  reveal Klon.calidObjects();
  assert left.calid();
  assert right.calid();
  assert left.calidObjects();
  assert right.calidObjects();
  assert mapLEQ(left.m, right.m);
  assert left.m.Keys <= right.m.Keys;
  assert subset <= left.m.Keys <= right.m.Keys;
}


///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
//actual cloning methods


method Clone_Via_Map(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //entry point for Clone - clones a according to map m'
  //call with m' empty
  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 20 //Clone_Via_Map

  requires m'.calid()
  requires a in m'.oHeap  //technically redundant given COKx
  requires COK(a, m'.oHeap)

  //extraOK  requires a.extra == {} //extra not yet cloned               HERE

  //ensures  (m.oHeap - m.m.Keys) < (m'.oHeap - m'.m.Keys)

  ensures  m.calid()
  //includes CallOK(m.oHeap)
  //includes CallOK(m.m.Keys, m.oHeap)
  //ensures  a.region.Heap? == b.region.Heap?

  ensures  a in m.m.Keys
  ensures  a in m.m.Keys
  ensures  b in m.m.Values
  ensures  b in m.m.Values
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b,m.oHeap+m.ns)

  //should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.m.Keys >= m'.m.Keys + {a}
  ensures  m.m.Values >= m'.m.Values + {b}
  ensures  m.from(m')

  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
  //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
  ensures  klonVMapOK(m.m)
  ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
  // should we say something about b.AMFO?  b.AMFO <= m.m.Values? por again m.hasV(b)?
  // m.key(a)?  m.val(a)???
  ensures  m.from(m')
  //ensures b.AMFO == set x <- a.AMFO :: m.m[x]


  // ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
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

  print "CALL Clone_Via_Map:", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

  print "VARIANT CVM ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 20, "\n";

  assert COKSTART: COK(a, m.oHeap);

  print "Clone_Via_Map started on:", fmtobj(a), "\n";

  //if already in hash table - return it and be done!
  //not sure why this takes sooo long compared to other
  if (a in m.m.Keys) {

    assert (a in m.m.Keys) by {
      reveal m.calid();
      assert m.calid();
      reveal m.calidObjects();
      assert m.calidObjects();
      assert m.m.Keys == m.m.Keys;
    }

    b := m.m[a];

    assert (b in m.m.Values) by {
      reveal m.calid();
      assert m.calid();
      reveal m.calidObjects();
      assert m.calidObjects();
      assert b == m.m[a];
      assert b in m.m.Values;
      assert m.m.Values == m.m.Values;
      assert b in m.m.Values;
    }

    assert CallOK(m.m.Values, m.oHeap+m.ns) by
    {
      reveal m.calid();
      assert m.calid();
      reveal m.calidObjects();
      assert m.calidObjects();
      reveal m.calidOK();
      assert m.calidOK();
    }

    COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
    assert COK(b, m.oHeap+m.ns);




    assert klonVMapOK(m.m) && (a.AMFO <= m.m.Keys)  by
    {
      reveal m.calid();
      assert m.calid();
      reveal m.calidOK();
      assert m.calidOK();
      reveal m.calidObjects();
      assert m.calidObjects();
      reveal m.calidMap();
      assert m.calidMap();
      assert m.m.Keys == m.m.Keys;
      assert klonVMapOK(m.m) && a.AMFO <= m.m.Keys;
      assert klonVMapOK(m.m) && a.AMFO <= m.m.Keys;
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

    print "RETN Clone_Via_Map: ", fmtobj(a)," already cloned,  returning ",fmtobj(b), "\n";

    return;
  } // a in m.Keys, already cloned

  assert unchanged(a) && unchanged(m.oHeap);

  assert a !in m.m.Keys;
  assert a !in m'.m.Keys;

  // assert a !in m.m.Values;
  // assert a !in m'.m.Values;

///case analysis...
  if (outside(a,m.o)) {
    print "Clone_Via_Map ", fmtobj(a), " is really outside ", fmtobj(m.o), "so maps to itself (share not clone)\n";

      assert  //KJX keeping this for now but... 
        && (a !in m.m.Keys)
        && (a !in m.ns)
        && (m.m.Values == m.m.Values)
      by {
        reveal m.calid();
        assert m.calid();
        reveal m.calidOK();
        assert m.calidOK();
        reveal m.calidObjects();
        assert m.calidObjects();
        reveal m.calidMap();
        assert m.calidMap();
        assert m.m.Keys == m.m.Keys;
        reveal m.calidSheep();
        assert m.calidSheep();
        assert a !in m.m.Keys;
        assert a in m.oHeap;
        assert m.oHeap !! m.ns;
        assert a in m.oHeap;
        assert m.m.Values == m.m.Values;
      }

      m.WeAreDevo();
      Klon.AintNoSunshine(a,m);

      assert a !in m.m.Values by {
        assert a !in m.m.Values;
        assert m.m.Values == m.m.Values;
        assert a !in m.m.Values;
      }

      print "Hey Baby let's CLONE Outside\n";

      b := a;

  assert b.fieldModes == a.fieldModes;

      print "Yay babhy hyou got that done\n";


  assert a !in m.m.Keys;
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
  assert m.m.Keys <= m.oHeap;
  OutsidersArentMapValues(a,m);

  reveal m.calidMap();
  assert m.calidMap();
  assert klonVMapOK(m.m);
  assert (forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys);
  assert m.m.Keys == m.m.Keys;
  assert (forall x <- m.m.Keys :: x.allExternalOwners() <= m.m.Keys);

  assert a !in m.m.Values;
  print "about to putOutside\n";
  m := m.putOutside(a);   ///HOPEY?  CHANGEY?
    print "crashy?  washy?\n";
  assert b.fieldModes == a.fieldModes;

  assert (b == a) by {
    assert not(inside(a, m.o));   //glurk
    assert m.AreWeNotMen(a,m);
    assert b == a;      //double glurk
  }



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

    assert a in m.m.Keys;
    assert b.fieldModes == a.fieldModes;

print "returnin' from the outsidee case\n";

    // assert a !in m'.m.Keys ==> b !in m'.ns;   //KJX sure about this?

    return;  //we may as well just return here.
             //we've done all we need to do.  I think.

  }///END OF THE OUTSIDE CASE
  else
  { //start of the Inside case
print "start of the Inside case\n";
      print "Clone_Via_Map owners:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";

      b, m := Clone_Clone_Clone(a, m);

      // assert a !in m'.m.Keys ==> b !in m'.ns;  }  //end of inside case


print "end of the Inside case\n";

  } //end of inside case

  /////////////////////////////////////////////////////////////// 
  //tidying up after the cases..

  // assert a !in m'.m.Keys ==> b !in m'.ns;   //KJX sure about this?

  reveal m.calid();
  assert m.calid();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidOK();
  assert m.calidOK();
  assert CallOK(m.m.Values, m.oHeap+m.ns);
  assert b in m.m.Values;
  assert m.m.Values == m.m.Values;
  assert b in m.m.Values;
  COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
  assert COK(b, m.oHeap+m.ns);
  //  assert fresh(b);   //umm, yeah should probalboy be fresh at least if INSIDE, but...
  //  have to experiment with a clause somewhere in calidSheep saying every inside clone is new
  //  or everyhing in ns is new. or...
  assert b in m.ns;

  assert m.m[a] == b;
  assert a !in m'.m.Keys;
  assert b !in m'.oHeap;
  //assert b !in m'.ns;


  //  assert  b.fields.Keys == {};

  assert  b.fieldModes.Keys == a.fieldModes.Keys;

  reveal m.calidSheep();
  assert m.calidSheep();

  assert  b.fieldModes == a.fieldModes;

  //  assert a !in m'.m.Keys ==> b !in m'.ns;   //KJX sure about this?

  //  assert m.from(m') by {
  //      reveal m.from();
  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns    >= m'.ns;

  assert m.from(m');
  //  }
  print "RETN Clone_Via_Map:", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

}





method Clone_All_Fields(a : Object, b : Object, m' : Klon)
  returns (m : Klon)
  //clone field a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10 //Clone_All_Fields

  requires MPRIME: m'.calid()
  requires COK(a, m'.oHeap)
  requires COK(b, m'.oHeap+m'.ns)

  requires b.fields.Keys == {}

  requires a.fields.Keys <= a.fieldModes.Keys
  requires a.fieldModes == b.fieldModes


  requires a in m'.oHeap
  requires a in m'.m.Keys

  requires b in m'.m.Values
  requires b in m'.ns
  requires (a in m'.m.Keys) && m'.m[a] == b
  requires m'.o    in m'.oHeap
  requires m'.m.Keys   <= m'.oHeap

  requires a.AMFO <= m'.m.Keys  //seems weird but we are populating m, right...

  // requires b.fieldModes[n] == Evil //evilKJX this is actually evil
  //well not *that* evil as I still must satisfy refOK
  //  
  // requires forall n <- b.fields :: (n in b.fieldModes) &&
  //             AssignmentCompatible(b, b.fieldModes[n], b.fields[n])

  //consequently
  //   requires refOK(a, a.fields[n])

  ensures  m.calid()
  ensures  old(m'.calid())
  ensures  klonVMapOK(m.m)
  ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...

  ensures  b.fields.Keys == a.fields.Keys

  ensures  a in m.m.Keys
  ensures  (a in m.m.Keys) && m.m[a] == b



  //   ensures  n in b.fields
  //   ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]

  ensures  b in m.m.Values

  ensures  mapLEQ(m'.m,m.m)

  ensures  CallOK(m.oHeap)
  ensures  COK(a, m.oHeap)
  ensures  COK(b, m.oHeap+m.ns)
  ensures  CallOK(m.m.Values, m.oHeap+m.ns)
  ensures  CallOK(m.ns, m.oHeap+m.ns)

  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns    >= m'.ns
  ensures  m.m.Keys    <= m.oHeap

  ensures a.fieldModes == b.fieldModes
  ensures b.fields.Keys == a.fields.Keys

  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.ns - {b})  //will this work?

  ensures  forall x <- (m.m.Values - {b}) :: old(allocated( x )) ==> unchanged( x ) //duesb;t veruft....

  //  modifies (set o : Object | o !in m'.oHeap)`fields
  // modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns?
  modifies b`fields   ///GGRRR
{
  m := m';

  print "CALL Clone_All_Fields: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

  assert m'.calid() by { reveal MPRIME; }

  assert BINNS:  b in m.ns;
  print "VARIANT CAF ", |(m'.oHeap - m'.m.Keys +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";
  print "<<<<<<<<<<<\n";
  print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
  print "<<<<<<<<<<<\n";


  assert unchanged(a) && unchanged(m.oHeap);

  assert  m.o == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns == m'.ns;
  assert  m.m.Values == m'.m.Values;

  assert  m.m.Keys == m'.m.Keys;
  assert  a in m'.m.Keys;

  assert m.m[a] == b;  //mmmKJX
  // assert (a in m.m.Keys) ==> (m[a] == b);  //mmmKJX

  assert m.calid();
  assert m'.calid() by { reveal MPRIME; }
  assert COK(b, m.oHeap+m.ns);
  assert HEREB: COK(b, m.oHeap+m.ns);




  //assert fresh(b);
  assert  b.fields.Keys == {};
  assert b in m.m.Values;

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
  assert CallOK(m.m.Values, m.oHeap+m.ns);

  assert CallOK(m.m.Keys, m.oHeap) by {}



  var rm := m;

  assert  rm.o     == m.o      == m'.o;
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns;
  assert  rm.m.Values    >= m.m.Values     >= m'.m.Values;
  assert  m.m.Keys     <= rm.m.Keys    <= m.oHeap;


  COKgetsDeclaredFields(a, m.oHeap);
  assert unchanged(a) && unchanged(m.oHeap);
  assert CallOK(m.m.Keys, m.oHeap);


  for i := 0 to |ns|

    invariant  rm.o     == m.o      == m'.o
    invariant  rm.oHeap == m.oHeap  == m'.oHeap
    invariant  rm.ns    >= m.ns     >= m'.ns
    invariant  rm.m.Values    >= m.m.Values     >= m'.m.Values
    invariant   m.m.Keys    <= rm.m.Keys    <= m.oHeap

    invariant  b in m.ns
    invariant  b in m.m.Values

    invariant COK(a, m.oHeap)
    invariant COK(b, m.oHeap+m.ns)
    invariant mapLEQ(m'.m,m.m)
    invariant a in m.oHeap
    invariant a in m.m.Keys
    invariant m.o in m.oHeap
    invariant CallOK(m.oHeap)
    invariant CallOK(m.m.Keys, m.oHeap)
    invariant CallOK(m.ns, m.oHeap+m.ns)
    invariant CallOK(m.m.Values, m.oHeap+m.ns)
    invariant m.calid()
    invariant old(m'.calid())

    invariant unchanged(a)
    invariant unchanged(m.oHeap)
    //invariant forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.at(x) == x))
    invariant (m'.oHeap - m'.m.Keys +{a}) >= (m.oHeap - m.m.Keys +{a})
    invariant (m'.oHeap - m'.m.Keys) >= (m.oHeap - m.m.Keys)
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
    print "  TLOOP m:", |m.oHeap - m.m.Keys|, " m':", |m'.oHeap - m'.m.Keys|, "\n";
    print "  TLOOP b.fieldsKeys==", b.fields.Keys, "\n";
    print "  TINV                ", ns[..i], "\n";
    print "  TLOOPINV            ",seq2set(ns[..i]),"\n";


    print "VARIANT*CAF ", |(m'.oHeap - m'.m.Keys +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";


    //   assert (m.oHeap - m.m.Keys) < (m'.oHeap - m'.m.Keys);

    assert  rm.o     == m.o      == m'.o;
    assert  rm.oHeap == m.oHeap  == m'.oHeap;
    assert  rm.ns    >= m.ns     >= m'.ns;
    assert  rm.m.Keys    >= m.m.Keys     >= m'.m.Keys;
    assert  rm.m.Values    >= m.m.Values     >= m'.m.Values;
    assert  m.m.Keys     <= rm.m.Keys    <= m.oHeap;

    assert b in m.ns by { reveal BINNS; assert b in m.ns; }
    assert n !in b.fields;
    assert refOK(a, a.fields[n])
    by {
      assert m.calid();  reveal m.calid();
      assert m.calidOK(); reveal m.calidOK();
      assert COK(a,m.oHeap); reveal COK();
      assert a.AllOutgoingReferencesAreOwnership(m.oHeap);
      assert  refOK(a, a.fields[n]);
      // - inside(f,t.owner);
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
    assert b in m.m.Values;
    assert a in m.m.Keys;



    var v_caf := ((m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10);
    var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map

    print "v_caf ", v_caf, "\n";
    print "v_cfm ", v_cfm, "\n";

    assert b.fields.Keys == seq2set(ns[..i]);
    assert a.fields.Keys == seq2set(ns);

    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) >  (m.oHeap - m.m.Keys +{a}), "\n";
    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) == (m.oHeap - m.m.Keys +{a}), "\n";

    assert (m'.oHeap - m'.m.Keys +{a}) >= (m.oHeap - m.m.Keys +{a});
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
    assert  rm.m.Keys    >= m.m.Keys     >= m'.m.Keys;
    assert  rm.m.Values    >= m.m.Values     >= m'.m.Values;
    assert  m.m.Keys     <= rm.m.Keys    <= m.oHeap;

    //   assert old@B4CLONEFIELD(forall x <- m'.m.Keys :: x.fieldModes == m'.m[x].fieldModes);
    //   assert (forall x <- m'.m.Keys :: x.fieldModes == old@B4CLONEFIELD(x.fieldModes));
    //   assert (forall x <- m'.m.Keys :: m'.m[x].fieldModes == old@B4CLONEFIELD(m'.m[x].fieldModes));
    //   assert (forall x <- m'.m.Keys :: x.fieldModes == m'.m[x].fieldModes);
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
    //         assert (m'.m.Keys <= m'.oHeap);
    //         assert (m'.m.Values <= m'.oHeap+m'.ns);
    //         assert COK(m'.o, m'.oHeap);
    //         assert CallOK(m'.oHeap);
    //         assert CallOK(m'.m.Keys, m'.oHeap);
    // 
    //         assert CallOK(m'.m.Values-{b}, m'.oHeap+m'.ns) by
    //           {
    // 
    //           }
    // 
    //         assert CallOK(m'.ns-{b}, m'.oHeap+m'.ns) by
    //           {
    //              
    //           }
    // 
    //         // assert CallOK(m'.m.Values, m'.oHeap+m'.ns);
    //         // assert CallOK(m'.ns, m'.oHeap+m'.ns);
    // 
    //             reveal m'.calidOK();
    //             assert m'.calidOK();
    //             reveal m'.calidObjects();
    //             // assert m'.calidObjects();
    //             reveal m'.calidMap();
    //             // assert m'.calidMap();
    //             assert m'.m.Keys == m'.m.Keys;
    // 
    //         reveal m'.AreWeNotMen();
    //         //reveal UniqueMapEntry();
    //         
    //         assert (forall x <- m'.m.Keys :: m'.AreWeNotMen(x, m'));
    //         assert (forall x <- m'.m.Keys :: x.fieldModes == m'.m[x].fieldModes);
    //         assert AllMapEntriesAreUnique(m'.m);
    // 
    //             reveal m'.calidSheep();
    //             assert m'.calidSheep();
    // 
    //    assert m'.calid(); }
    //    


    assert  CallOK(m.m.Keys, m.oHeap)
    by { reveal m.calid();    assert m.calid();
         reveal m.calidOK();  assert m.calidOK();
       }


  } //end of loop

  assert unchanged(a) && unchanged(m.oHeap);


  //DONE FIELDS

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
  assert a in m.m.Keys;
  assert b in m.oHeap+m.ns;

  assert COK(b, m.oHeap+m.ns);

  assert mapLEQ(m'.m,m.m);


  assert CallOK(m.oHeap);
  assert COK(a, m.oHeap);
  assert COK(b, m.oHeap + m.ns);
  assert CallOK(m.m.Values, m.oHeap+m.ns);
  assert COK(b, m.oHeap  + m.ns);


  reveal m.calidObjects(); assert m.calidObjects();


  assert COK(m.o, m.oHeap);
  assert CallOK(m.oHeap);
  assert CallOK(m.m.Keys, m.oHeap);
  assert CallOK(m.m.Values, m.oHeap+m.ns);
  assert CallOK(m.ns, m.oHeap+m.ns);

  reveal m.calidOK(); assert m.calidOK();

  reveal m.calidMap(); assert m.calidMap();

  assert klonVMapOK(m.m);



  assert  rm.o     == m.o      == m'.o;
  assert  rm.oHeap == m.oHeap  == m'.oHeap;
  assert  rm.ns    >= m.ns     >= m'.ns;
  assert  rm.m.Values    >= m.m.Values     >= m'.m.Values;

  reveal m.calidObjects(); assert m.calidObjects();
  reveal m.calidOK(); assert m.calidOK();
  reveal m.calidSheep(); assert m.calidSheep();

  assert m.m.Keys == m.m.Keys;

  reveal m.AreWeNotMen();
  assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
  assert forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.m[x] == x));

  assert  b.fieldModes == a.fieldModes;

  reveal m.calid(); assert m.calid();

  // assert m'.calid() by { reveal MPRIME; }

  assert klonVMapOK(m.m) && a.AMFO <= m.m.Keys;
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
  print "RETN Clone_All_Fields done ", fmtobj(a), "\n";

  return;
}
//end Clone_All_Fields





// method Clone_Outside_Heap(a : Object, m' : Klon)
//   returns (b : Object, m : Klon)
//   decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Outside_Heap

//   //extraOK  requires a.extra == {} //extra not yet cloned

//   //this case
//   requires a !in m'.m.Keys
//   requires a !in m'.m.Values
//   requires outside(a,m'.o)

//   //all Clone_
//   requires m'.calid()
//   requires a in m'.oHeap
//   requires COK(a, m'.oHeap) //bonus - covered in the above :-)

//   ensures  m.calid()
//   ensures  a == b
//   ensures  a in m.m.Keys
//   ensures  a in m.m.Keys
//   ensures  b in m.m.Values
//   ensures  b in m.m.Values
//   ensures  a in m.m.Keys && m.at(a) == b
//   ensures  COK(b, m.oHeap+m.ns)

//   //should I package this up - as aw twostate or a onestate?
//   ensures  mapLEQ(m'.m,m.m)
//   ensures  m.m.Keys >= m'.m.Keys + {a}
//   ensures  m.m.Values >= m'.m.Values + {b}
//   ensures  m.o == m'.o
//   ensures  m.oHeap == m'.oHeap
//   ensures  m.ns >= m'.ns
//   //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//                           //this means that on return, every owner is now in the map...
//   ensures m.from(m')

//   //ensures b.AMFO == set x <- a.AMFO :: m.m[x]

//   ensures b.fieldModes == a.fieldModes
//   //  ensures b.fields.Keys == a.fields.Keys

//   //  modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
//   // ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
//   modifies {}
// {
//   m := m';

//   assert m.m.Keys == m'.m.Keys;
//   assert a !in m.m.Keys;
//   assert a !in m.m.Values;

//   assert m == m';
//   assert m.m == m'.m;
//   assert mapLEQ(m'.m,m.m);
//   assert m.from(m');

//   print "Clone_Outside_Heap outside owners:", fmtobj(a), " owned by ", fmtobj(a.owner) ,"\n";
//   print "VARIANT COH ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

//   assert CallOK(m.oHeap) by {
//     reveal m.calid();
//     assert m.calid();
//     reveal m.calidOK();
//     assert m.calidOK();
//     reveal CallOK();
//     assert CallOK(m.oHeap);
//   }

//   assert (a.Ready() && a.Valid()) by {
//     reveal CallOK();
//     assert CallOK(m.oHeap);
//     assert a in m.oHeap;
//     COKfromCallOK(a, m.oHeap);
//     reveal COK();
//     assert COK(a, m.oHeap);
//     assert a.Ready();
//     assert a.Valid();
//   }


//   assert a.OwnersValid() by {
//     assert a.Ready();
//     assert a.Valid();
//     assert a.OwnersValid();
//   }

//   // argh OVERKILL - won't work...
//   //    assert a.AMFO <= m.m.Keys by {
//   // 
//   //           assert COK(a, m.oHeap);
//   //           reveal m.calid();
//   //           assert m.calid();
//   //           reveal m.calidObjects();
//   //           assert m.calidObjects();
//   //           reveal m.calidOK();
//   //           assert m.calidOK();
//   //           reveal m.Klon();
//   //           assert m.Klon();
//   // 
//   //           assert m.m.Keys == m.m.Keys;
//   //           assert klonVMapOK(m.m);
//   //           assert forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys;
//   //    }




//   assert CallOK(a.owner, m.oHeap) by {
//     assert a.OwnersValid();
//     assert a.AMFO > flattenAMFOs(a.owner);
//     assert CallOK(m.oHeap);
//     COKfromCallOK(a, m.oHeap);
//     reveal COK();
//     assert COK(a, m.oHeap);
//     a.CallMyOwnersWillWitherAway(a, m.oHeap);
//     assert CallOK(a.owner, m.oHeap);
//   }


//   //preconditions for the call..
//   // assert m.calid();
//   // assert a.owner <= m.oHeap;
//   assert CallOK(a.owner, m.oHeap);
//   // assert outside(a.owner, m.o); //TEMP TO WRITEOUTSIDE CASE

//   //extraOK reveal COK(); assert a.extra == {}; //extra not yet cloned

//   var rowner, rm := Clone_Via_Map(a.owner, m);

//   assert rowner in rm.m.Values;
//   //assert rowner.AMFO <= rm.m.Values;  //shouild be able ot do this p- it follows
//   assert a.owner <= rm.m.Keys;
//   assert flattenAMFOs(a.owner) <= rm.m.Keys;

//   assert flattenAMFOs(a.owner) <= rm.m.Keys;
//   assert a.AMFO == flattenAMFOs(flattenAMFOs(a.owner)) + {a};

//   assert rm.from(m);
//   assert rm.from(m');
//   assert klonVMapOK(rm.m);
//   reveal rm.calid(); assert rm.calid();
//   reveal rm.calidObjects(); assert rm.calidObjects();
//   assert rm.m.Keys == rm.m.Keys;
//   reveal rm.calidMap(); assert  rm.calidMap();
//   assert (forall x <- rm.m.Keys, oo <- x.AMFO :: rm.m[oo] in rm.m[x].AMFO);
//   assert (forall x <- rm.m.Keys,     oo <- x.AMFO :: rm.m[oo] in rm.m[x].AMFO);
//   assert rm.m.Keys >= m'.m.Keys;
//   assert mapLEQ(m'.m,rm.m);
//   assert rm.from(m);

// ///WHY THE FuCK DO I NEED TO DO THIS?
// ///BEST GUESS TO EnSURE ALL The OWNERS of a are in the map
// ///becuse it's outside it shouldn't actually CLONE ANYTHING

// ///BUT things hop around insidef, e.g. so we've already copied "a" in the recursive call
// ///can we just be done?
// ///Hmm. fuck I hate this shit

//   //Hmm do we even need to do this?
//   //or won't the recursive call handle it anyway??
//   if (a in rm.m.Keys) {
//     m := rm;
//     assert m.from(rm);
//     reveal m.calid();
//     assert m.calid();
//     reveal m.calidObjects();
//     assert m.calidObjects();
//     reveal m.calidSheep();
//     assert m.calidSheep();

//     assert m.at(a).fieldModes == a.fieldModes;
//     b := m.at(a);
//     assert b == m.m[a];

//     assert (b == a) by {
//       assert not(inside(a, m.o));   //glurk
//       reveal m.AreWeNotMen();
//       assert m.AreWeNotMen(a,m);
//       assert ((not(inside(a, m.o))) ==> (m.m[a] == a));
//       assert (m.m[a] == a);
//       assert (m.m[a] == m.at(a) == a);
//       assert b == a;      //double glurk
//     }

//     assert b.fieldModes == a.fieldModes;

//     reveal m.calidOK();
//     assert m.calidOK();
//     assert CallOK(m.m.Values, m.oHeap+m.ns);
//     assert b in m.m.Values;
//     assert m.m.Values == m.m.Values;
//     assert b in m.m.Values;
//     COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
//     assert COK(b, m.oHeap+m.ns);

//     assert b.fieldModes == a.fieldModes;
//     assert m.from(m');
//     return; //should work because Clone_Via_Map meets all the conditiosn, right???
//   }  //end if a in rm.m.Keys


//   assert a !in rm.m.Keys;
//   assert a !in rm.m.Values by {


//     assert not(inside(a,rm.o));
//     assert a !in rm.m.Keys;
//     assert rm.calid();
//     rm.WeAreDevo();
//     assert forall k <- rm.m.Keys :: rm.AreWeNotMen(k,rm);
//     assert a  in rm.oHeap;
//     assert a !in rm.ns;



//     Klon.AintNoSunshine(a, rm);
//     assert a !in rm.m.Values; }
//   assert rm.m.Keys >= m'.m.Keys;
//   assert mapLEQ(m'.m,rm.m);
//   assert rm.from(m');

//   //    //maintaing klonVMapOK
//   //         assert AMFOOKRM: a.allExternalOwners() <= rm.m.Keys by {
//   //             reveal rm.calid();
//   //             assert rm.calid();
//   //             reveal rm.calidMap();
//   //             assert rm.calidMap();
//   //             assert klonVMapOK(rm.m);
//   //             reveal rm.calidObjects();
//   //             assert rm.calidObjects();
//   //             assert (forall x <- rm.m.Keys, oo <- x.AMFO :: oo in rm.m.Keys);
//   //             assert a.allExternalOwners() <= rm.m.Keys by {
//   //                reveal COK();
//   //                assert COK(a,m.oHeap);
//   //                assert a.AMFO <= m.oHeap;
//   // //               assert a.allExternalOwners() <= rm.m.Keys;
//   //                }
//   //         }5



//   assert a in rm.oHeap;
//   assert COK(a, rm.oHeap);
//   reveal COK();
//   assert a.AMFO <= rm.oHeap;
//   //  assert a.allExternalOwners() <= rm.m.Keys;
//   OutsidersArentMapValues(a,rm);
//   assert a !in rm.m.Values;
//   assert a !in rm.m.Keys;
//   assert not(inside(a, rm.o));

//   //m := rm[a:=b];



//   assert rm.calid();
//   assert a in rm.oHeap;
//   assert COK(a, rm.oHeap);

//   assert CallOK(rm.oHeap) by {
//     reveal rm.calid(), rm.calidOK();
//     assert rm.calid();
//     assert rm.calidOK();
//     reveal CallOK(), COK();
//     assert CallOK(rm.oHeap);
//   }


//   var xm := rm;
//   assert xm.m.Keys >= m'.m.Keys;
//   assert mapLEQ(m'.m,xm.m);
//   assert xm.from(rm);
//   assert xm.from(m');

//   assert a !in xm.m.Keys;
//   assert a !in xm.m.Values;


//   var MX := a.owner - xm.m.Keys;
//   assert MX <= a.owner;
//   var xo : Object;
//   var rr : Object;
//   var oldmks  : set<Object>;  //dont fucking ask
//   var oldmok :=  false;

//   assert !oldmok;
//   assert xm == rm;
//   assert xm.m.Keys >= (m'.m.Keys);
//   assert mapLEQ(m'.m,xm.m);
//   assert xm.from(m');

//   assert a !in xm.m.Keys;

//   while ((MX != {}) && (a !in xm.m.Keys))
//     decreases MX
//     invariant MX == a.owner - xm.m.Keys
//     invariant MX <= a.allExternalOwners()
//     invariant xm == rm
//     invariant xm.calid()
//     invariant rm.calid()
//     invariant old(m'.calid())
//     invariant xm.from(m')
//     invariant MX <= xm.oHeap
//     invariant CallOK(xm.oHeap)
//     invariant a.AMFO - {a} <= xm.m.Keys + MX
//     invariant oldmok ==> assigned(oldmks)
//     invariant oldmok ==> (xm.m.Keys > oldmks)
//     invariant m'.oHeap == xm.oHeap
//     invariant oldmok ==> ((m'.oHeap - oldmks) > (xm.oHeap - xm.m.Keys))
//     invariant xm.m.Keys >= (m'.m.Keys)
//     invariant xm.m.Values >= (m'.m.Values)
//     invariant a !in xm.m.Keys
//   {
//     assert xm == rm;
//     xo :| xo in MX;
//     assert xo in MX;
//     MX := MX - {xo};

//     assert xm.calid();
//     assert xo in xm.oHeap;
//     COKfromCallOK(xo,xm.oHeap);
//     assert COK(xo,xm.oHeap);
//     assert xo !in xm.m.Keys;


//     assert oldmok ==> (m'.oHeap - oldmks) > (xm.oHeap - xm.m.Keys);

//     assert xo in a.AMFO;
//     assert a.Ready();
//     assert a.AMFO > xo.AMFO;


//     assert (m'.oHeap) == m'.oHeap == xm.oHeap;
//     assert xm.m.Keys >= (m'.m.Keys);
//     assert xm.from(m');

//     assert  mapLEQ(m'.m,xm.m) by
//     { reveal xm.calid(); assert xm.calid();
//       reveal xm.calidObjects(); assert xm.calidObjects();
//       assert m'.m.Keys <= xm.m.Keys;
//       assert m'.m.Values <= xm.m.Values;
//       assert m'.m.Keys == m'.m.Keys;
//       assert m'.m.Values == m'.m.Values;
//       assert xm.m.Keys == xm.m.Keys;
//       assert xm.m.Values == xm.m.Values;
//       assert m'.m.Keys <= xm.m.Keys;
//       assert m'.m.Values <= xm.m.Values;
//       assert forall k <- m'.m.Keys :: k in xm.m.Keys;
//       assert forall k <- m'.m.Keys :: k in xm.m.Keys && (m'.m[k] == xm.m[k]);
//     }

//     // 
//     //                   assert xm.m.Keys >= m'.m.Keys;
//     //                 assert a !in xm.m.Keys;
//     // 
//     //           assert ((m'.oHeap - m'.m.Keys)) >= (xm.oHeap - xm.m.Keys);
//     // 
//     // assert  ((a.AMFO)
//     //   decreases to
//     //         (xo.AMFO));
//     //       
//     //         assert ((m'.oHeap - m'.m.Keys),
//     //                (a.AMFO),
//     //                (a.fields.Keys),
//     //                (15)
//     //           decreases to
//     //                xm.oHeap - xm.m.Keys,
//     //                xo.AMFO,
//     //                xo.fields.Keys,
//     //                20);


//     rr, rm := Clone_Via_Map(xo, xm);
//     assert rm.m.Keys >= m'.m.Keys;
//     assert mapLEQ(m'.m,rm.m);
//     assert rm.from(m');

//     if (a in rm.m.Keys) {
//       m := rm;
//       assert m.calidObjects() by {  reveal m.calid(); assert  m.calid();  }
//       assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
//       assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
//       b := m.m[a];
//       //

//       assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects();  assert b in m.m.Values; }
//       assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects(); }
//       assert m.calidOK() by {  reveal m.calid(); assert  m.calid();  }
//       assert  a in m.m.Keys && m.at(a) == b;
//       assert  COK(b, m.oHeap+m.ns) by {
//         assert b in m.m.Values;
//         assert CallOK(m.m.Values, m.oHeap+m.ns) by { reveal m.calidOK(); }
//         COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);   }

//       assert m.from(m');

//       assert  mapLEQ(m'.m,m.m) by
//       { reveal m.calidObjects(); assert m.calidObjects();
//         assert m'.m.Keys <= m.m.Keys;
//         assert mapLEQ(m'.m,m.m);
//         assert m'.m.Keys <= m.m.Keys;
//         assert m'.m.Values <= m.m.Values;
//       }
//       assert  m.m.Keys >= m'.m.Keys + {a} by { reveal m.calidObjects(); assert m.calidObjects(); }
//       assert  m.m.Values >= m'.m.Values + {b} by { reveal m.calidObjects(); assert m.calidObjects(); }
//       assert  m.o == m'.o;
//       assert  m.oHeap == m'.oHeap;
//       assert  m.ns >= m'.ns;
//       assert klonVMapOK(m.m);
//       assert forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys;
//       assert  a in m.m.Keys;
//       assert forall oo <- a.AMFO :: oo in m.m.Keys;
//       assert a.AMFO <= m.m.Keys;
//       assert m.m.Keys == m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
//       assert a.AMFO <= m.m.Keys;



//       assert  a == b by {
//         reveal m.calid();
//         assert m.calidMap();
//         reveal m.calidMap();
//                //    assert (forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.m[x] == x)));
//         assert not(inside(a,m.o));
//         assert m.m[a] == a;
//         assert a == b;
//       }

//       assert (b.fieldModes == a.fieldModes) by { assert a == b; }

//       return;
//     }  // if a is in m.Keys after clone -- if it got added magically...

//     assert xo in rm.m.Keys;
//     assert xm != rm;
//     //    assert rr == xo;

//     MX := MX - rm.m.Keys;
//     assert rm.m.Keys > xm.m.Keys;
//     oldmks := xm.m.Keys;
//     oldmok := true;
//     xm := rm;
//     assert xm.m.Keys >= m'.m.Keys;
//     assert xm.m.Keys > oldmks;

//     assert xm.from(m');


//     //          MX := a.extra - rm.m.Keys;
//     assert xm == rm;
//   } // end loop MX


//   assert xm == rm;
//   assert xm.m.Keys >= m'.m.Keys;
//   assert a !in xm.m.Keys;
//   assert (a.AMFO - {a})<= xm.m.Keys;


//   assert xm.calid(); assert rm.calid();
//   assert a.AMFO - {a} <= rm.m.Keys;
//   //  SubsetOfKeysOfExtendedMap(a.AMFO , rm, m);
//   assert a.allExternalOwners() ==  a.AMFO - {a};
//   assert a.AMFO == flattenAMFOs(a.owner) + {a};
//   assert a.allExternalOwners() <= rm.m.Keys;
//   assert xm.m.Keys >= m'.m.Keys;
//   assert xm.from(m');
//   assert a !in xm.m.Keys;

//   assert a !in xm.m.Keys by { assert a !in xm.m.Keys; }
//   assert COK(a,xm.oHeap);
//   assert a.Ready();
//   assert a.AllOwnersAreWithinThisHeap(xm.m.Keys);
//   assert a.allExternalOwners() <= xm.m.Keys;
//   assert (a.AMFO - {a}) <= xm.m.Keys;
//   assert (forall oo <- (a.AMFO - {a}) :: oo in xm.m.Keys);
//   //  assert (xm.m[a].region.Heap?);
//   assert (a.owner <= a.AMFO);
//   assert (a.owner <= xm.m.Keys);
//   //  assert (xm.m[a.owner] == xm.m[a].owner );
//   //  assert (forall oo <- a.AMFO :: xm.m[oo] in xm.m[a].AMFO);

//   //  assert (forall xo <- a.extra :: xm.m[xo] in xm.m[a].extra) ;

//   assert a !in rm.m.Keys;
//   rm.WeAreDevo();
//   assert a !in rm.m.Values  by { Klon.AintNoSunshine(a, rm); }
//   m := rm.putOutside(a);
//   b := m.at(a);
//   assert b == a;
//   assert b.fieldModes == a.fieldModes;


//   assert m.at(a).fieldModes == a.fieldModes;
//   b := m.at(a);
//   assert b == m.m[a];

//   // why wias this still here?????
//   //         assert (b == a) by {
//   //           assert not(inside(a, m.o));   //glurk
//   //           reveal m.AreWeNotMen();
//   //           assert m.AreWeNotMen(a,m);
//   //           assert ((not(inside(a, m.o))) ==> (m.m[a] == a));
//   //           assert (m.m[a] == a);
//   //           assert (m.m[a] == m.at(a) == a);
//   //           assert b == a;      //double glurk
//   //         }

//   assert COK(b, m.oHeap);
//   COKWiderContext(b, m.oHeap, m.ns);
//   assert COK(b, m.oHeap+m.ns);

//   assert m.m == MappingPlusOneKeyValue(rm.m,a,b);
//   assert m.calid();
//   MapOKFromCalid(m);
//   assert klonVMapOK(m.m);
//   assert mapLEQ(rm.m, m.m);
//   assert m.from(rm);  assert m.from(m');
//   //    assert a.allExternalOwners() <= rm.m.Keys by { reveal AMFOOKRM; }
//   assert a.AMFO - {a}  <= rm.m.Keys;
//   //      SubsetOfKeysOfExtendedMap(a.AMFO, rm, m);
//   assert a.allExternalOwners() <= m.m.Keys;
//   assert a in m.m.Keys;
//   assert a.AMFO == a.allExternalOwners() + {a};
//   assert a.AMFO <= m.m.Keys;

//   assert b.fieldModes == a.fieldModes;

//   //END outside  HEAP OBJECT
// }



// method Clone_Outside_World(a : Object, m' : Klon)
//   returns (b : Object, m : Klon)
//   decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Outside_World

//   //extraOK  requires a.extra == {} //extra not yet cloned

//   //this case
//   requires a !in m'.m.Keys
//   requires a !in m'.m.Values
//   requires outside(a,m'.o)

//   //all Clone_
//   requires m'.calid()
//   requires a in m'.oHeap
//   requires COK(a, m'.oHeap)


//   ensures  m.calid()
//   ensures  a in m.m.Keys
//   ensures  a in m.m.Keys
//   ensures  b in m.m.Values
//   ensures  b in m.m.Values
//   ensures  a in m.m.Keys && m.at(a) == b
//   ensures  COK(b, m.oHeap+m.ns)

//   //should I package this up - as aw twostate or a onestate?
//   ensures  mapLEQ(m'.m,m.m)
//   ensures  m.m.Keys >= m'.m.Keys + {a}
//   ensures  m.m.Values >= m'.m.Values + {b}
//   ensures  m.o == m'.o
//   ensures  m.oHeap == m'.oHeap
//   ensures  m.ns >= m'.ns
//   //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//   ensures m.from(m')

//   //ensures b.AMFO == set x <- a.AMFO :: m.m[x]

//   ensures a.fieldModes == b.fieldModes
//   // ensures b.fields.Keys == a.fields.Keys
//   // modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
//   // ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
//   modifies {}
// {
//   m := m';


//   assert ANKS: a !in m.m.Keys;

//   assert COK(a,m.oHeap);
//   reveal COK();
//   assert a.Ready();
//   assert a.AMFO == {a};

//   reveal m.calid();
//   assert m.calid();
//   reveal m.calidOK();
//   assert m.calidOK();
//   reveal m.calidSheep();
//   assert m.calidSheep();

//   print "Clone_Via_Map world:", fmtobj(a),"\n";
//   print "VARIANT COW ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";
//   assert CallOK(m.oHeap);

//   b := a;
//   assert b.fieldModes == a.fieldModes;




//   assert a !in m.m.Keys;
//   assert a in m.oHeap;
//   assert m.oHeap !! m.ns by {
//     reveal m.calidObjects();
//     assert m.calidObjects();
//     assert m.oHeap !! m.ns;
//   }
//   assert outside(a,m.o);
//   a.CallMyOwnersWillWitherAway(a, m.oHeap);

//   reveal m.calidObjects();
//   assert m.calidObjects();
//   assert m.m.Keys <= m.oHeap;
//   OutsidersArentMapValues(a,m);

//   reveal m.calidMap();
//   assert m.calidMap();
//   assert klonVMapOK(m.m);
//   assert (forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys);
//   assert m.m.Keys == m.m.Keys;
//   assert (forall x <- m.m.Keys :: x.allExternalOwners() <= m.m.Keys);

//   assert a !in m.m.Values;
//   m := m.putOutside(a);   ///HOPEY?  CHANGEY?
//   assert b.fieldModes == a.fieldModes;

//   assert (b == a) by {
//     assert not(inside(a, m.o));   //glurk
//     assert m.AreWeNotMen(a,m);
//     assert b == a;      //double glurk
//   }

// }





method Clone_KaTHUMP(a : Object, m' : Klon)
  //spike method to test AMFO being "owner-closed"
  //means the clones are "owner-cooned"
  // that all the owners (and their AMFOS) are in the current objects AMFOS
  //  i.e,  forall oo <- MYOWNERS :: oo in oo.AMFO
  //  forall oo <- MYOWNERS - this? :: oo.AMFO <= this.AMFO..
  // so if .e.g a[x] == c,   then we want m[a[x]] == m[c]...
  // (please James, write a comment about what yhis method is doing]
  returns (b : Object, m : Klon)
  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_Heap

  //this case
  requires a !in m'.m.Keys
  requires inside(a,m'.o)

  //extraOK  requires a.extra == {} //extra not yet clone


  //all Clone_
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)

  //from clone extra owners
  ensures  m.calid() //needed to be able to call some of the below  en
  //ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...  //kathump
  ensures  m.from(m')

  // ensures  a !in m'.m.Keys ==> b !in m'.ns
  // ensures  b  in m'.ns ==> a  in m'.m.Keys

{ //kathump

  m := Clone_All_Owners(a, m');
  b := a;  //OOPS!  //KJX WHAT THE FUICKY FUCK FUCK

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
  assert a.owner <= a.AMFO;
  assert COK(m.o, m.oHeap);
  assert CallOK(m.oHeap);
  COKAMFO(a, m.oHeap);
  assert CallOK(a.AMFO, m.oHeap);
  assert a.owner <= a.AMFO;
  CallOKNarrowFocus(a.owner, m.oHeap);
  assert CallOK(a.owner, m.oHeap);

  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //

  assert AllTheseOwnersAreFlatOK(a.AMFO - {a});
  //  reveal AllTheseOwnersAreFlatOK();
  assert OrigBigfoot(a.AMFO - {a});

  assert flattenAMFOs(a.owner) == a.allExternalOwners();
  assert OrigBigfoot(a.allExternalOwners());
  assert AllTheseOwnersAreFlatOK(a.allExternalOwners()) by
  {
    reveal AllTheseOwnersAreFlatOK();
    assert AllTheseOwnersAreFlatOK(a.allExternalOwners());
  }
  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //


  // assert a.allExternalOwners() <= m.m.Keys;

  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //


  assert  m.from(m');


  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //

  // assert  a !in m'.m.Keys ==> b !in m'.ns;
  // assert  b  in m'.ns ==> a  in m'.m.Keys;
}





method Clone_Clone_Clone(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_Heap

  //this case
  requires a !in m'.m.Keys
  requires inside(a,m'.o)

  //extraOK  requires a.extra == {} //extra not yet cloned


  //all Clone_
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)

  //requires CallOK(a.extra,m'.oHeap); ///now covered by the above?

  ensures  m.calid()
  ensures  a in m.m.Keys
  ensures  a in m.m.Keys
  ensures  b in m.m.Values
  ensures  b in m.m.Values
  ensures  b in m.ns
  ensures  a in m.m.Keys && m.at(a) == b
  ensures  COK(b, m.oHeap+m.ns)

  //on reflection, none of these make sense - or perhaps this one does?
  //  ensures  b.fields == map[]

  //should I package this up - as aw twostate or a onestate?
  //it;s about clonbamps, so clonmapLEQ or clonmapEXTENDS
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.m.Keys >= m'.m.Keys + {a}
  ensures  m.m.Values >= m'.m.Values + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
  //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
  ensures klonVMapOK(m.m)
  ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
  ensures old(m'.calid())
  ensures m.from(m')

  //ensures b.AMFO == set x <- a.AMFO :: m.m[x]

  ensures b.fieldModes == a.fieldModes
  //   ensures b.fields.Keys == a.fields.Keys

  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  //modifies (set o : Object)`fields
  // ensures a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?   //Cline INsinside heap
  // ensures b in m'.ns ==> a in m'.m.Keys
  modifies {}
{ //clone inside heap
  m := m';

  assert COK(a, m.oHeap);
  assert aFLAT: AllTheseOwnersAreFlatOK(a.AMFO - {a}) by {
    reveal COK();
    reveal AllTheseOwnersAreFlatOK();
    assert COK(a, m.oHeap);
    assert AllTheseOwnersAreFlatOK(a.AMFO - {a});
    assert a.owner <= a.AMFO;
    assert a !in a.owner;
    assert a.owner <= (a.AMFO - {a});
    assert AllTheseOwnersAreFlatOK(a.owner);
    assert (a.AMFO - {a}) == flattenAMFOs(a.owner);  //yuck - flatten a.owner or flattenAMFOs(a.owner)s or what?
  }
  assert m.calid();
  assert inside(a,m.o);



  assert ANKS: a !in m.m.Keys;
  assert COKFOURWAYS: m.calid();

  print "Clone_Clone_CLone of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CIH ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";
  assert CallOK(a.owner, m.oHeap) by {
    assert m.calid();
    reveal m.calid();
    assert m.calidOK();
    reveal m.calidOK();
    COKfromCallOK(a, m.oHeap);
    assert COK(a, m.oHeap);
    reveal COK();
    assert a.Ready();
    assert a.owner <= a.AMFO;
    assert COK(m.o, m.oHeap);
    assert CallOK(m.oHeap);
    COKAMFO(a, m.oHeap);
    assert CallOK(a.AMFO, m.oHeap);
    assert a.owner <= a.AMFO;
    CallOKNarrowFocus(a.owner, m.oHeap);
    assert CallOK(a.owner, m.oHeap);

  }

  //makde COK check for this, no need to do another level here?
  // assert forall x <- a.extra :: COK(x,m.oHeap);
  // forall x <- a.extra ensures COK(x,m.oHeap)
  // {
  //   assert true;
  // }
  //assert CallOK(a.extra,m.oHeap);

  assert (flattenAMFOs(a.owner) < a.AMFO) by {
    assert m.calid();
    reveal m.calid();
    assert m.calidOK();
    reveal m.calidOK();
    COKfromCallOK(a, m.oHeap);
    assert COK(a, m.oHeap);
    reveal COK();   
    assert a.Ready();
    assert a.AMFO > flattenAMFOs(a.owner);
    assert flattenAMFOs(a.owner) <=  a.AMFO;
  }

  print "Clone_Clone_CLone ", fmtobj(a), " calling Clone_All_Owners", fmtown(a.owner) ,"\n";


  //extraOK        reveal COK(); assert a.owner.extra == {}; //extra not yet cloned

  var rm := Clone_All_Owners(a, m);
  assert rm.from(m);

  assert a.owner <= m.m.Keys;


  var rowner := mapThruKlon(a.owner, rm);

  print "Clone_Clone_CLone ", fmtobj(a), " Clone_All_Owners RETURNS ", fmtown(rowner) ,"\n";


  assert CallOK(rowner, rm.oHeap+rm.ns);

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

  assert CallOK(a.owner, rm.oHeap);
  assert CallOK(rm.oHeap);
  assert CallOK(rm.m.Keys, rm.oHeap);
  assert CallOK(rm.m.Values, rm.oHeap+rm.ns);
  assert CallOK(rm.ns, rm.oHeap+rm.ns);



  //should we rename oHeap as context?

  assert COK(rm.o, rm.oHeap);
  assert CallOK(rm.oHeap);


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

  assert CallOK(rowner, rm.oHeap+rm.ns);  //ensured by clone

///need this for later...
  assert OKR0: CallOK(rowner, rm.oHeap+rm.ns);
  assert OKC0: CallOK(rm.oHeap+rm.ns);


  if (a in rm.m.Keys) {

    print "Clone_Clone_CLone ", fmtobj(a), " already cloned: abandoning ship!!\n";


    m := rm;
    b := rm.at(a);
    assert m.calid();
    assert CallOK(m.m.Values, m.oHeap+m.ns);
    assert b in m.m.Values;
    assert m.m.Values == m.m.Values;
    assert b in m.m.Values;
    assert (b in m.ns) by
    {
      reveal m.calid();
      assert m.calid() && m.calidObjects() && m.calidOK() && m.calidSheep();
      reveal m.calidSheep();
      reveal m.AreWeNotMen();
      assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
      assert b == m.m[a];
      assert a in m.m.Keys;
      assert inside(a,m.o);
      assert m.m[a] in m.ns;
      assert b in m.ns;
    }
    assert b in m.ns;
    assert b in rm.ns;

    COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
    assert COK(b, m.oHeap+m.ns);
    assert COK(b, rm.oHeap+rm.ns);

    assert b.fieldModes == a.fieldModes;
    assert m.calidSheep();

    assert m.m.Keys >= m'.m.Keys + {a};
    assert m.m.Values >= m'.m.Values + {b};

    return;
  } // a in rm.m.Keys - i.e. randomly done while cloning owners

  print "Clone_Clone_CLone ", fmtobj(a), " have rowner ", fmtown(rowner) ," self not yet cloned\n";

  assert a !in rm.m.Keys;
  assert a.owner <= rm.m.Keys;

  assert CallOK(rowner, rm.oHeap+rm.ns);
  assert CallOK(rm.oHeap+rm.ns);
  CallOKNarrowFocus({},rm.oHeap+rm.ns);    //WTF is this doiung?  why?
  assert CallOK({},rm.oHeap+rm.ns);        //and this one?


///need this for later...
  assert OKR1: CallOK(rowner, rm.oHeap+rm.ns);
  assert OKC1: CallOK(rm.oHeap+rm.ns);


  var rrm := Clone_All_Owners(a, rm);
  assert rrm.from(rm);

  assert CallOK(rrm.oHeap);
  assert CallOK(rrm.oHeap, rrm.oHeap);
  assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);
  CallOKWiderContext(rrm.oHeap, rrm.oHeap, rrm.ns);
  CallOKWiderFocus(rrm.oHeap, rrm.ns, rrm.oHeap+rrm.ns);
  assert OKC2: CallOK(rrm.oHeap+rrm.ns);

///need this for later...

  //COKWiderContext2(rowner, )

  CallOKWiderContext2(rowner, rm.oHeap+rm.ns, rrm.oHeap+rrm.ns);
  assert OKR2: CallOK(rowner, rrm.oHeap+rrm.ns);


  assert a.owner <= rm.m.Keys;
  assert a.owner <= rrm.m.Keys;

  if (a in rrm.m.Keys) {

    print "Clone_Clone_Clone ", fmtobj(a), "after Clone_Extra_Oners, seems a already cloned: abandoning ship!!\n";

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
    assert (forall x <- rrm.m.Keys :: rrm.AreWeNotMen(x, rrm));
    assert rrm.AreWeNotMen(a,rrm);
    assert (inside(a,rrm.o)) ==> rrm.m[a] in rrm.ns;
    assert b == rrm.m[a];

    assert b in rrm.ns;
    assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);
    COKfromCallOK(b, rrm.ns, rrm.oHeap+rrm.ns);
    assert COK(b, rrm.oHeap+rrm.ns);

    return;
  }

  assert a !in rrm.m.Keys;

  assert rrm.m.Keys <= rrm.oHeap;

print "Clone_Clone_Clone ", fmtobj(a), " boodle boodle boodle\n";



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
  assert a.allExternalOwners() <= rrm.oHeap;
  assert a !in rrm.m.Keys; // by { reveal ANKS; }

  assert OKR3: CallOK(rowner, rrm.oHeap+rrm.ns);
  assert OKC3: CallOK(rrm.oHeap+rrm.ns);

  //preconditions for cake...
  assert CallOK(rowner, rrm.oHeap+rrm.ns) by { reveal OKR3, OKC3; }
  assert CallOK(rrm.oHeap+rrm.ns) by { reveal OKR3, OKC3; }


  assert (a.AMFO - {a}) == a.allExternalOwners();
  assert flattenAMFOs(a.AMFO - {a}) == flattenAMFOs(a.allExternalOwners());

  assert a.allExternalOwners() + {a} == a.AMFO;
  // assert flattenAMFOs(a.owner) + a.extra == (a.AMFO - {a}) == a.allExternalOwners();
  // 
  // reveal AllTheseOwnersAreFlatOK();
  // 
  //        assert AllTheseOwnersAreFlatOK(a.AMFO - {a}) by { reveal aFLAT; }
  //        assert AllTheseOwnersAreFlatOK(flattenAMFOs(a.owner) + a.extra);
  var aAMFOs := a.allExternalOwners() + {a};
  //  assert AllTheseOwnersAreFlatOK(aAMFOs);https://www.youtube.com/



  //assert forall ax <- a.extra :: imageUnderMap(ax, rrm.m[ax], rrm);
  assert rowner == mapThruKlon(a.owner, rrm);
  assert a.allExternalOwners() <= rrm.m.Keys;
  //assert forall ao <- flattenAMFOs(a.owner) :: rrm.m[ao] in (rrm.m[a.owner]).AMFO;




  assert OrigBigfoot(flattenAMFOs(a.owner));
  assert AllTheseOwnersAreFlatOK(flattenAMFOs(a.owner));



  //reveal AllTheseOwnersAreFlatOK();

  //assert rowner.AMFO ==  mapThruKlon(flattenAMFOs(a.owner), rrm);
  //        assert AllTheseOwnersAreFlatOK(flattenAMFOs(a.owner) + a.extra);
  // 
  //        assert AllTheseOwnersAreFlatOK(rowner.AMFO);
  // 
  //        assert AllTheseOwnersAreFlatOK(a.extra, a.allExternalOwners());


  // 
  //       assert (set o <- a.extra ::  rrm.m[o]) == mapThruKlon(a.extra, rrm);
  //       assert (set o <- a.extra, oo <- o.AMFO ::  rrm.m[oo])
  //          == mapThruKlon((set o <- a.extra, oo <- o.AMFO :: oo), rrm);
  // 
  // assert mapThruKlon(aAMFOs, rrm) == amfosToBeMinusThis;

  //  assert ((set o <- a.extra, oo <- o.AMFO :: oo) + a.extra)   //tnis should not worj!!!
  //           ==  flattenAMFOs(mapThruKlon(a.extra,rrm));

  reveal AllTheseOwnersAreFlatOK();
  assert AllTheseOwnersAreFlatOK(rowner); ///this one is OK...
  assert OrigBigfoot(rowner);



  var R := rrm.m;
  assert AllMapEntriesAreUnique(R);

  assert klonVMapOK(R);

  assert  (forall x <- R.Keys, oo <- x.AMFO  :: R[oo] in R[x].AMFO);

  assert flattenAMFOs(a.owner) <= R.Keys;

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

////KJX  assert rowner.AMFO <= amfosToBeMinusThis;

  reveal AllTheseOwnersAreFlatOK();

  //       var R := rrm.m;
  //       assert AllMapEntriesAreUnique(R);
  //       var M := invert(R);
  //       assert AllMapEntriesAreUnique(M);
  // 
  //       assert forall r <- R.Keys :: M[R[r]] == r;


  //assert (forall o <- rextra :: o.AMFO <=  (rowner.AMFO+rextra));
  // assert (forall o <- rextra, oo <- o.AMFO :: ((oo in rowner.AMFO) || (oo in rextra)));
  // assert (forall o <- rextra :: o.AMFO <=  (rowner.AMFO+rextra));


  assert Bigfoot(rowner);  //both originally had a .AMFO on the end - do we need it?  yes?  no?  what's the difference?
  assert AllTheseOwnersAreFlatOK(rowner);

  // assert Bigfoot((rextra), (rowner.AMFO+rextra));
  // assert AllTheseOwnersAreFlatOK((rextra), (rowner.AMFO+rextra));

  var context := rrm.oHeap+rrm.ns;
  assert CallOK(rowner, context);
  assert CallOK(context);

  assert AllTheseOwnersAreFlatOK(rowner);//both originally had a .AMFO on the end - do we need it?  yes?  no?  what's the difference?


print "CALLING MAKE...";
  b := new Object.make(a.fieldModes, rowner, rrm.oHeap+rrm.ns, "clone of " + a.nick);
print "BACK FROM MAKE with ",fmtobj(b),"\n";


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


  assert b !in rrm.m.Values;
  assert COK(b, rrm.oHeap+rrm.ns+{b});
  assert b !in (rrm.oHeap+rrm.ns);

  assert klonVMapOK(rrm.m);
  //assert forall kx <- a.extra :: rrm.m[kx] in b.extra;   //extra not yet cloned

  //extraOK        assert a.extra == {}; //extra not yet cloned
  assert a.allExternalOwners() <= rrm.m.Keys;

  var xm := rrm.putInside(a,b);
  assert xm.m == MappingPlusOneKeyValue(rrm.m,a,b);

  assert xm.m.Keys >= rrm.m.Keys + {a};
  assert xm.m.Values >= rrm.m.Values + {b};
  assert b in xm.ns;
  assert COK(b, xm.oHeap+xm.ns);

  MapOKFromCalid(xm);
  assert xm.calid();

  print "Clone_CLone_Clone map updated ", fmtobj(a), ":=", fmtobj(b) ,"\n";


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
  assert a in xm.m.Keys;
  assert b in xm.m.Values;
  assert b in xm.ns;
  assert (a in xm.m.Keys) && xm.m[a] == b;
  assert xm.o    in xm.oHeap;
  assert xm.m.Keys   <= xm.oHeap;


///WHAT THE FUCK FUCKUY FUCK IS GOING ON FUCKY HERE
  // assert (m'.oHeap - m'.m.Keys) >=  (xm.oHeap - xm.m.Keys +{a});
  // assert old((a.fields.Keys)) >= (a.fields.Keys);


  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   /////    /////    /////   /////    /////    /////   /////    /////

  m := xm;

  m := Clone_All_Fields(a,b, xm);

  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   /////    /////    /////   /////    /////    /////   /////    /////



  assert m.m.Keys >= xm.m.Keys;
  assert m.m.Values >= xm.m.Values;

  assert m.m.Keys >= m'.m.Keys + {a};
  assert m.m.Values >= m'.m.Values + {b};

  print "Clone_Clone_CLone of ", fmtobj(a), " retuning ", fmtobj(b) ,"\n";
}











// method Clone_Inside_World(a : Object, m' : Klon)
//   returns (b : Object, m : Klon)
//   decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_World(

//   //this case
//   requires inside(a,m'.o)
//   requires a.region.World?
//   requires a !in m'.m.Keys

//   //extraOK  requires a.extra == {} //extra not yet cloned

//   //all Clone_
//   requires m'.calid()
//   requires a in m'.oHeap
//   requires COK(a, m'.oHeap)


//   ensures  m.calid()
//   ensures  a in m.m.Keys
//   ensures  a in m.m.Keys
//   ensures  b in m.m.Values
//   ensures  b in m.m.Values
//   ensures  b in m.ns
//   ensures  a in m.m.Keys && m.at(a) == b
//   ensures  COK(b, m.oHeap+m.ns)

//   ensures  b.fields.Keys == a.fields.Keys

//   // ensures fresh(b)

//   //should I package this up - as aw twostate or a onestate?
//   ensures  mapLEQ(m'.m,m.m)
//   ensures  m.m.Keys >= m'.m.Keys + {a}
//   ensures  m.m.Values >= m'.m.Values + {b}
//   ensures  m.o == m'.o
//   ensures  m.oHeap == m'.oHeap
//   ensures  m.ns >= m'.ns
//   //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//   ensures m.from(m')

//   ensures b.fieldModes == a.fieldModes
//   //   ensures b.fields.Keys == a.fields.Keys
//   // ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
//   modifies {}
// {
//   m := m';

//   //  assert  m.m.Keys >= m'.m.Keys + {a};
//   //  assert  m.m.Values >= m'.m.Values + {b};

//   print "VARIANT CIW ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

//   assert COK(a, m.oHeap);
//   assert m.calid();
//   assert inside(a,m.o);
//   m.DevoIsUnique();
//   assert AllMapEntriesAreUnique(m.m);

//   assert ANKS: a !in m.m.Keys;
//   assert COKFOURWAYS: m.calid();


//   reveal m.calid();
//   assert m.calid();
//   reveal m.calidOK();
//   assert m.calidOK();

//   print "Clone_Via_Map world:", fmtobj(a),"\n";

//   assert CallOK(m.oHeap);

//   assert BEFORE: m.calid();

//   b := new Object.frozen2(a.fieldModes, m.oHeap);

//   b.nick := "clone of " + a.nick;

//   assert fresh@BEFORE(b);
//   assert b !in m.oHeap;
//   assert b !in m.ns;
//   assert unchanged@BEFORE(m.oHeap`fields, m.oHeap`fieldModes);
//   assert unchanged@BEFORE(m.ns`fields, m.ns`fieldModes);

//   assert m.calid();

//   assert fresh(b);
//   assert b !in m.oHeap + m.ns;
//   assert COK(a, m.oHeap); // by { reveal COKSTART; }
//   assert COK(b, m.oHeap+{b});
//   COKWiderContext(b, m.oHeap+{b}, m.ns);
//   assert (m.oHeap+{b})+m.ns == m.oHeap+m.ns+{b};
//   assert COK(b, m.oHeap+m.ns+{b});

//   assert a !in m.m.Keys by { reveal ANKS; }  //was m.m.Keys...
//   assert a !in m.m.Keys by { reveal ANKS;  reveal m.calid(); assert m.calid(); reveal m.calidObjects(); assert m.calidObjects(); }  //was m.m.Keys...

//   RVfromCOK(a, m.oHeap);
//   var mx := m.putInside(a,b);

//   assert (mx.m.Keys == mx.m.Keys && mx.m.Values == mx.m.Values)
//   by {
//     reveal m.putInside();
//     assert mx.calid(); reveal mx.calid();
//     assert mx.calidObjects(); reveal mx.calidObjects();
//   }
//   assert mx.m == m.m[a:=b];
//   assert mx.m == MappingPlusOneKeyValue(m.m,a,b);

//   assert  mx.m.Keys >= m'.m.Keys + {a};
//   assert  mx.m.Values >= m'.m.Values + {b};

//   assert COK(b, mx.oHeap+mx.ns);

//   reveal mx.calidMap();
//   assert mx.calid();
//   reveal mx.calidMap();
//   assert mx.calidMap();
//   assert klonVMapOK(mx.m);

//   assert a.AMFO == {a};
//   assert a.AMFO <= mx.m.Keys;

//   m := Clone_All_Fields(a,b, mx);

//   assert  (m.m.Keys >= mx.m.Keys && m.m.Values >= mx.m.Values)
//   by {
//     assert m.calid();
//     reveal m.calid();
//     assert m.calidObjects();
//     reveal m.calidObjects();
//   }

//   assert  m.m.Keys >= m'.m.Keys + {a};
//   assert  m.m.Values >= m'.m.Values + {b};

// }




















method Clone_Field_Map(a : Object, n : string, b : Object, m' : Klon)
  returns (m : Klon)
  //clone field a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5 //Clone_Field_Map

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
  requires a in m'.m.Keys

  requires b in m'.m.Values
  requires b in m'.ns
  requires (a in m'.m.Keys) && m'.m[a] == b
  requires m'.o    in m'.oHeap
  requires m'.m.Keys   <= m'.oHeap

  requires b.fieldModes == a.fieldModes

  // requires b.fieldModes[n] == Evil //evilKJX this is actually evil
  //well not *that* evil as I still must satisfy refOK

  requires forall n <- b.fields :: (n in b.fieldModes) &&
                                   AssignmentCompatible(b, b.fieldModes[n], b.fields[n])

  //consequently
  requires refOK(a, a.fields[n])



  ensures  b.fields.Keys == old(b.fields.Keys) + {n}
  ensures  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys)
  ensures  m.calid()
  ensures  old(m'.calid())


  ensures  a in m.m.Keys
  ensures  (a in m.m.Keys) && m.m[a] == b

  ensures  n in b.fields
  ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]

  ensures  b in m.m.Values

  ensures  mapLEQ(m'.m,m.m)

  ensures  CallOK(m.oHeap)
  ensures  COK(a, m.oHeap)
  ensures  COK(b, m.oHeap+m.ns)
  ensures  CallOK(m.m.Values, m.oHeap+m.ns)
  ensures  CallOK(m.ns, m.oHeap+m.ns)

  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns    >= m'.ns
  ensures  m.m.Keys    >= m'.m.Keys
  ensures  m.m.Values    >= m'.m.Values
  ensures  m.m.Keys    <= m.oHeap


  ensures klonVMapOK(m.m)
  ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...

  ensures old(m'.calid())
  ensures m.from(m')

  ensures a.fieldModes == b.fieldModes

  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.m.Values - {b})
  ensures  unchanged(m'.m.Keys)

  //ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
  //  in this case, a should be in kis, b in b',ns

  ensures  unchanged(m'.ns - {b})  //will this work?

  //  ensures unchanged(m.m.Values - {b}) //duesb;t veruft....

  //  modifies (set o : Object | o !in m'.oHeap)`fields
  // modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns?
  modifies b`fields
{
  assert m'.calid() by { reveal MPRIME; }
  assert unchanged(m'.ns);

  m := m';

  var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map

print "CALL Clone_Field_Map ", fmtobj(a), " «", n, "»\n";

  print "VARIANT CFM ", |(m'.oHeap - m'.m.Keys)+{a}|, " ", |a.AMFO|, " ", |(a.fields.Keys - b.fields.Keys - {n})|, " ", 10, "\n";

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

  assert rfv in  rm.oHeap+rm.m.Values;
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
     //   assert ofv.owner == a; //KJX what should this be>?
        assert b == rm.m[a];
        assert rfv == rm.m[ofv];
     //   assert b == rfv.owner;
        // assert b == rm.m[a.fields[n].owner];
        // assert b == rfv.owner;
        assert AssignmentCompatible(b, b.fieldModes[n], rfv);

      case Peer =>
        assert AssignmentCompatible(a, a.fieldModes[n], ofv);
        assert a.owner == ofv.owner;
        // if a.region.Heap? {
          assert (mapThruKlon(a.owner, rm) == b.owner);
          assert mapThruKlon(ofv.owner, rm) == rfv.owner;
          assert rfv.owner == b.owner;
          assert b.owner == rfv.owner;
        // } else {
        //   assert AssignmentCompatible(a, a.fieldModes[n], rfv);
        // }
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
    && CallOK(m.m.Values, m.oHeap+m.ns)
    && CallOK(m.ns, m.oHeap+m.ns)
    && ( m.m.Keys    <= m.oHeap )
  by { reveal m.calid(); reveal m.calidOK(); }

  CallOKNarrowFocus(m.m.Values-{b}, m.m.Values, m.oHeap+m.ns);
  CallOKNarrowFocus(m.ns-{b}, m.ns, m.oHeap+m.ns);

  assert CallOK(m.m.Values-{b}, m.oHeap+m.ns);
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);

  assert b in m.ns;

  label JUSTBEFORE:

  b.fields := b.fields[n := rfv];

  assert unchanged(m'.ns - {b});

  assert CallOK(m.m.Values-{b}, m.oHeap+m.ns);
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);


  assert m.m[ofv] == rfv; 
  assert rfv in m.m.Values;
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
    && CallOK(m.m.Values, m.oHeap+m.ns)
    && CallOK(m.ns, m.oHeap+m.ns)
  by {
    assert CallOK(m.m.Values-{b}, m.oHeap+m.ns); //OK
    assert CallOK(m.ns-{b}, m.oHeap+m.ns);

    assert COK(b, m.oHeap+m.ns);
    assert b in  m.oHeap+m.ns by { reveal COK(); }
    CallOKfromCOK(b, m.oHeap+m.ns);
    CallOKWiderFocus(m.ns-{b}, {b}, m.oHeap+m.ns);
    assert (m.ns-{b} + {b}) == m.ns;

    assert b in m'.m.Values;
    assert b in  m.m.Values;

    assert m.m.Values <= m.oHeap+m.ns by { reveal m.calid(); reveal m.calidOK(); }

    assert COK(b, m.oHeap+m.ns);
    assert b in  m.oHeap+m.ns by { reveal COK(); }
    CallOKfromCOK(b, m.oHeap+m.ns);
    CallOKWiderFocus(m.m.Values-{b}, {b}, m.oHeap+m.ns);
    assert (m.m.Values-{b} + {b}) == m.m.Values;


    assert CallOK(m.m.Values, m.oHeap+m.ns);
    assert CallOK(m.ns, m.oHeap+m.ns);
  }

  //OLDCALID assert m'.calid() by { reveal MPRIME; }

  assert  m.calidOK()
  by {
    assert old@B4(rm.calidOK());
    reveal m.calidOK();

    assert old@B4(CallOK(m.m.Values, m.oHeap+m.ns));
    assert old@B4(CallOK(m.ns, m.oHeap+m.ns));


    assert rfv in rm.m.Values;
    assert rfv in rm.oHeap+rm.ns;
    assert COK(rfv,m.oHeap+m.ns);

    assert (m.o in  m.oHeap);
    assert (m.m.Keys <= m.oHeap);
    assert (m.m.Values <= m.oHeap+m.ns);
    assert COK(m.o, m.oHeap);
    assert CallOK(m.oHeap);
    assert CallOK(m.m.Keys, m.oHeap);

    assert COK(b,m.oHeap+m.ns);

    // assert CallOK(m.m.Values, m.oHeap+m.ns);
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

    assert m.m.Keys == m.m.Keys;
    reveal m.AreWeNotMen();
    assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
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




function mapThruKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
  requires m.calid()
  requires os <= m.m.Keys

  ensures  r  <= m.m.Values <= (m.oHeap + m.ns)
{
  reveal m.calid(), m.calidOK();
  set o <- os :: m.m[o]
}




lemma mapThruKlonKVIsNICE(os : set<Object>, m : Klon, k : Object, v : Object)
  requires os <= m.m.Keys + {k}
  requires k !in m.m.Keys //technically unnecessary but nice to have?
  requires v !in m.m.Values //technically unnecessary but nice to have?

  ensures  (set o <- os :: if (o == k) then (v) else (m.m[o]))  ==  (set o <- os :: m.m[k:=v][o])
  ensures  m.m[k:=v].Keys == m.m.Keys+{k}
  ensures  k in m.m[k:=v].Keys
  ensures  v in m.m[k:=v].Values
  ensures  forall x <- m.m.Keys :: x in m.m[k:=v].Keys
{
}

lemma mapThruMapKVisOK(os : set<Object>, m : Klon, k : Object, v : Object)
  requires m.calid()
  requires os <= m.m.Keys + {k}
  requires os <= m.m.Keys + {k}
  
  ensures mapThruKlonKV(os, m, k, v) == mapThruKlon(os, m.(m:= m.m[k:=v]))
{}




function  mapThruKlonKV(os : set<Object>, m : Klon, k : Object, v : Object) : (r : set<Object>)
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
  requires m.calid()
  requires os <= m.m.Keys + {k}

  ensures  r  <= m.m.Values + {v}
  ensures  r  <= (m.m.Values + {v}) <= (m.oHeap + m.ns + {v})
{
  reveal m.calid(), m.calidOK();
  set o <- os :: if (o == k) then (v) else (m.m[o])
}



lemma mapThruMapPreservesLessSameMore(less: set<Object>, same: set<Object>, more : set<Object>, m : Klon)
  requires m.calid()
  requires less <= m.m.Keys
  requires less <= m.m.Keys
  requires same <= m.m.Keys
  requires same <= m.m.Keys
  requires more <= m.m.Keys
  requires more <= m.m.Keys
  requires less == same
  requires less <  more
  requires same <  more
  ensures  mapThruKlon(less,m) == mapThruKlon(same,m)
  ensures  mapThruKlon(less,m) <= mapThruKlon(more,m)
  ensures  mapThruKlon(same,m) <= mapThruKlon(more,m)
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();

  BothSidesNow(m.m);

  assert forall l <- less :: l in same;
  assert forall l <- less :: l in more;
  assert forall s <- same :: s in less;

  assert forall l <- mapThruKlon(less,m) :: l in mapThruKlon(same,m);
  assert forall l <- mapThruKlon(less,m) :: l in mapThruKlon(more,m);
  assert forall s <- mapThruKlon(same,m) :: s in mapThruKlon(less,m);

  assert mapThruKlon(less,m) == mapThruKlon(same,m) <= mapThruKlon(more,m);
}


lemma MapThruMapPreservesSubsets(less: set<Object>, more : set<Object>, m : Klon)
  requires m.calid()
  requires less <= m.m.Keys
  requires less <= m.m.Keys
  requires more <= m.m.Keys
  requires more <= m.m.Keys
  requires less <= more
  ensures  mapThruKlon(less,m) <= mapThruKlon(more,m)
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  BothSidesNow(m.m);

  assert forall l <- less :: l in more;

  assert forall l <- mapThruKlon(less,m) :: l in mapThruKlon(more,m);

  assert mapThruKlon(less,m) <= mapThruKlon(more,m);
}



lemma MapThruMapPreservesSets(less: set<Object>, more : set<Object>, m : Klon)
  requires m.calid()
  requires less <= m.m.Keys
  requires less <= m.m.Keys
  requires more <= m.m.Keys
  requires more <= m.m.Keys
  requires less == more
  ensures  mapThruKlon(less,m) <= mapThruKlon(more,m)
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  BothSidesNow(m.m);

  MapThruMapPreservesSubsets(less, more, m);
  MapThruMapPreservesSubsets(more, less, m);

  assert mapThruKlon(less,m) == mapThruKlon(more,m);
}



lemma MapThruMapIsInvertible(less: set<Object>, other: set<Object>,  m : Klon)
//I hate the term "injective" must be a better one. invertible?
  requires m.calid()
  requires less <= m.m.Keys
  requires less <= m.m.Keys
  requires other == mapThruKlon(less, m)
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  BothSidesNow(m.m);
  reveal UniqueMapEntry();

  //var other :=  (set x <- less :: m.m[x]);
  //var other := mapThruKlon(less, m);

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




lemma MapThruMapSingleton(l : Object, m : Klon)
  requires m.calid()
  requires {l} <= m.m.Keys
  requires {l} <= m.m.Keys
  ensures  mapThruKlon({l},m) == {m.m[l]}
{
  assert (set o <- {l} :: m.m[o]) == {m.m[l]};
}

//WUY THE FUCK CAN"T I USE SOME OF THESE!!!



lemma MapThruMapPreservesAMFO(less: set<Object>, other : set<Object>, m : Klon)
  requires m.calid()
  requires less <= m.m.Keys
  requires less <= m.m.Keys
  requires other == mapThruKlon(less, m)
  //ensures  forall l <- less :: mapThruKlon(l.AMFO,m) == m.m[l].AMFO
  ensures  forall l <- less :: l.AMFO <= m.m.Keys
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
  assert klonVMapOK(m.m);

  reveal UniqueMapEntry();
  }


lemma MapThruMapKVExtendsAMFO(m : Klon, k : Object, v : Object)
  requires m.calid()
  requires k !in m.m.Keys
  requires v !in m.m.Values
  requires k.AMFO <= m.m.Keys+{k}
  requires v.AMFO <= m.m.Values+{v}  
  requires k in  m.oHeap
  requires v in  m.oHeap+m.ns
  requires mapThruKlonKV(k.AMFO, m, k, v) == v.AMFO

  requires
    && (k.AMFO <= m.m.Keys+{k})
    && ((k.owner <= k.AMFO))
    && ((k.owner <= m.m.Keys))
    && ((mapThruKlon(k.owner, m) == v.owner))



  ensures (
    var bb := m.m[k:=v];    
    && (forall x <- bb.Keys :: x.AMFO <= bb.Keys) 
    && (forall x <- bb.Keys :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO)
  )
   ///what it SHOULD BE
  // ensures  klonVMapOK(m.m[k:=v])
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
  assert klonVMapOK(m.m);

  reveal UniqueMapEntry();


  var aa : vmap<Object,Object> := m.m;

      assert //expanded body of klonVMapOK!
        && (forall x <- aa.Keys :: x.AMFO <= aa.Keys)
        && (forall x <- aa.Keys :: (set oo <- x.AMFO :: aa[oo]) == aa[x].AMFO)
        && (forall x <- aa.Keys :: x.owner <= x.AMFO)
        && (forall x <- aa.Keys :: x.owner <= aa.Keys)
        && (forall x <- aa.Keys :: mapThruKlon(x.owner, m) == aa[x].owner )
      ;  

assert k.AMFO <= m.m.Keys+{k};

assert v.AMFO == mapThruKlonKV(k.AMFO, m, k, v);
assert v.AMFO == (set oo <- k.AMFO :: if (oo == k) then (v) else (aa[oo]));

var bb : vmap<Object,Object> := aa[k:=v];

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

  assert mapThruKlonKV(k.AMFO, m, k, v) == v.AMFO;
  assert (set o <- k.AMFO :: if (o == k) then (v) else (aa[o])) == v.AMFO; 
  assert forall oo <- bb.Keys :: bb[oo] == (if (oo == k) then (v) else (aa[oo]));
  assert (set oo <- k.AMFO :: bb[oo]) == v.AMFO; 
}

assert  (forall x <- {k} :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO);






      assert //expanded body of klonVMapOK!
        && (forall x <- {k} :: x.AMFO <= bb.Keys)
        && (forall x <- {k} :: (set oo <- x.AMFO :: bb[oo]) == bb[x].AMFO)
        && (forall x <- {k} :: x.owner <= x.AMFO)
        && (forall x <- {k} :: x.owner <= bb.Keys)
        && (forall x <- {k} :: mapThruKlon(x.owner, m) == bb[x].owner)

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
          assert (forall x : Object <- (aa.Keys+{k}) :: (mapThruKlon(x.AMFO,m)) == bb[x].AMFO);
      }
}













method Clone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)

  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 12

  requires a !in m'.m.Keys //mustn't have cloned a yet...
  requires COK(a, m'.oHeap)
  requires m'.calid()

  ensures  m.calid()
  //ensures  a !in m.m.Keys //mustn't have cloned a yet...`
  //  ensures  a.AMFO <= m.m.Keys  //should beecome AMFO? - oh yep


  ensures  m.from(m')

  modifies {}
  //TODO  ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
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
  //   assert a !in rm.m.Values;
  //   assert a !in rm.m.Keys;
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
  assert xm.m.Keys >= m'.m.Keys;
  assert mapLEQ(m'.m,xm.m);
  assert xm.from(rm);
  assert xm.from(m');

  assert forall x <- a.AMFO  :: inside(a,x);



  var xo : Object;
  var rr : Object;
  var oldmks  : set<Object>;  //dont fucking ask
  var oldmok :=  false;

  assert !oldmok;
  assert xm == rm;
  assert xm.m.Keys >= (m'.m.Keys);
  assert mapLEQ(m'.m,xm.m);
  assert xm.from(m');

  var MX := a.owner;


  while ((MX != {}) && (a !in xm.m.Keys))
    decreases MX
    invariant MX == a.owner - xm.m.Keys
    invariant MX <= a.owner
    invariant forall x <- MX :: inside(a,x)
    invariant xm == rm
    invariant xm.calid()
    invariant rm.calid()
    invariant old(m'.calid())
    invariant xm.from(m')
    invariant MX <= xm.oHeap
    invariant CallOK(xm.oHeap)
    invariant a.owner - {a} <= xm.m.Keys + MX //this one?
    invariant a.owner <= a.AMFO
    invariant oldmok ==> assigned(oldmks)
    invariant oldmok ==> (xm.m.Keys > oldmks)
    invariant m'.oHeap == xm.oHeap
    invariant oldmok ==> ((m'.oHeap - oldmks) > (xm.oHeap - xm.m.Keys))
    invariant xm.m.Keys >= (m'.m.Keys)
    invariant xm.m.Values >= (m'.m.Values)
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
    assert xo !in xm.m.Keys;


    assert oldmok ==> (m'.oHeap - oldmks) > (xm.oHeap - xm.m.Keys);

    assert xo in a.AMFO;
    assert a.Ready();
    assert xo in a.owner;
    assert a.AMFO > xo.AMFO;


    assert (m'.oHeap) == m'.oHeap == xm.oHeap;
    assert xm.m.Keys >= (m'.m.Keys);
    assert xm.from(m');

    assert  mapLEQ(m'.m,xm.m) by
    {
      reveal xm.calid(); assert xm.calid();
      reveal xm.calidObjects(); assert xm.calidObjects();
      assert m'.m.Keys <= xm.m.Keys;
      assert m'.m.Values <= xm.m.Values;
      assert m'.m.Keys == m'.m.Keys;
      assert m'.m.Values == m'.m.Values;
      assert xm.m.Keys == xm.m.Keys;
      assert xm.m.Values == xm.m.Values;
      assert m'.m.Keys <= xm.m.Keys;
      assert m'.m.Values <= xm.m.Values;
      assert forall k <- m'.m.Keys :: k in xm.m.Keys;
      assert forall k <- m'.m.Keys :: k in xm.m.Keys && (m'.m[k] == xm.m[k]);
    }


    assert xm.m.Keys >= m'.m.Keys;
    assert a !in xm.m.Keys;

    assert ((m'.oHeap - m'.m.Keys)) >= (xm.oHeap - xm.m.Keys);

    assert ((a.AMFO) decreases to (xo.AMFO));

    assert ((m'.oHeap - m'.m.Keys),
            (a.AMFO),
            (a.fields.Keys),
            (15)
            decreases to
            xm.oHeap - xm.m.Keys,
            xo.AMFO,
            xo.fields.Keys,
            20);

    assert inside(a, xo);


    rr, rm := Clone_Via_Map(xo, xm);

    assert rm.m.Keys >= m'.m.Keys;
    assert mapLEQ(m'.m,rm.m);
    assert rm.from(m');

    if (a in rm.m.Keys) {
      m := rm;
      assert m.calidObjects() by {  reveal m.calid(); assert  m.calid();  }
      assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  a in m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      b := m.m[a];
      //

      assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects();  assert b in m.m.Values; }
      assert  b in m.m.Values by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert m.calidOK() by {  reveal m.calid(); assert  m.calid();  }
      assert  a in m.m.Keys && m.at(a) == b;
      assert  COK(b, m.oHeap+m.ns) by {
        assert b in m.m.Values;
        assert CallOK(m.m.Values, m.oHeap+m.ns) by { reveal m.calidOK(); }
        COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);   }

      assert m.from(m');
      assert  mapLEQ(m'.m,m.m) by
      { reveal m.calidObjects(); assert m.calidObjects();
        assert m'.m.Keys <= m.m.Keys;
        assert mapLEQ(m'.m,m.m);
        assert m'.m.Keys <= m.m.Keys;
        assert m'.m.Values <= m.m.Values;
      }
      assert  m.m.Keys >= m'.m.Keys + {a} by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  m.m.Values >= m'.m.Values + {b} by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert  m.o == m'.o;
      assert  m.oHeap == m'.oHeap;
      assert  m.ns >= m'.ns;
      assert klonVMapOK(m.m);
      assert forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys;
      assert  a in m.m.Keys;
      assert forall oo <- a.AMFO :: oo in m.m.Keys;
      assert a.AMFO <= m.m.Keys;
      assert m.m.Keys == m.m.Keys by { reveal m.calidObjects(); assert m.calidObjects(); }
      assert a.AMFO <= m.m.Keys;
      assert a.owner <= m.m.Keys;

      assert (b.fieldModes == a.fieldModes);

      return;
    }  // if a is in m.Keys after clone -- if it got added magically...

    assert xo in rm.m.Keys;
    assert xm != rm;

    MX := MX - rm.m.Keys;
    assert rm.m.Keys > xm.m.Keys;
    oldmks := xm.m.Keys;
    oldmok := true;
    xm := rm;
    assert xm.m.Keys >= m'.m.Keys;
    assert xm.m.Keys > oldmks;

    assert xm.from(m');

    assert xm == rm;
  } // end loop MX

  m := xm;
}










lemma MapOKFromCalid(m : Klon)
  requires m.calid()
  ensures  klonVMapOK(m.m)
{  ////
  reveal m.calid();
  reveal m.calidMap();
}



lemma  OutsidersArentMapValues(a : Object, m : Klon)
  requires m.calid()
  requires a in m.oHeap  //technically redundant
  requires COK(a, m.oHeap)
  requires outside(a,m.o) //TEMP TO WRITEOUTSIDE CASE
  requires a !in m.m.Keys
  ensures  a !in m.m.Values
{
  reveal m.calid();
  reveal m.calidObjects();
  assert m.calidObjects();
  reveal m.calidSheep();
  assert m.calidSheep();
  reveal m.AreWeNotMen();

  assert m.ns !! m.oHeap;
  assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);

  assert
    && (forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.m[x] == x)))
    && (forall x <- m.m.Keys ::    ((inside(x,m.o)) ==> (m.m[x] in m.ns)))
    ;

  if (a in m.m.Values) {
    AValueNeedsAKey(a,m.m);

    assert {:contradiction} not(outside(a,m.o));
    assert {:contradiction} false;
  }
}




lemma {:onlyClone} OwnersValidFromCalid(a : Object, m : Klon)
  requires m.calid()
  requires
    || COK(a, m.oHeap)
    || (CallOK(m.oHeap) && (a in m.oHeap))
    || (CallOK(m.m.Keys, m.oHeap) && (a in m.m.Keys))
    || (CallOK(m.m.Keys, m.oHeap+m.ns) && (a in m.m.Keys))
    || (CallOK(m.m.Keys, m.oHeap+m.ns) && (a in m.m.Keys))
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
    || (CallOK(m.m.Keys, m.oHeap) && (a in m.m.Keys) && a.Ready())
    || (CallOK(m.m.Keys, m.oHeap+m.ns) && (a in m.m.Keys) && a.Ready())
    || (CallOK(m.m.Keys, m.oHeap+m.ns) && (a in m.m.Keys) && a.Ready());

  assert a.Ready();
  assert a.OwnersValid();
}
















///aux lemmas etc

lemma  bNotInoHeap(b : Object, m : Klon)
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
 


















lemma PsychoBigFoot(os : set<Object>, context : set<Object> := os, m : Klon)
   requires m.calid()
   requires os <= m.m.Keys
   requires os <= m.m.Keys  
   requires context <= m.m.Keys
   requires context <= m.m.Keys  
   requires os <= context
   requires OrigBigfoot(os,context)

   ensures  m.calid()
   ensures  os <= m.m.Keys
   ensures  os <= m.m.Keys  
   ensures  context <= m.m.Keys
   ensures  context <= m.m.Keys  
   ensures  os <= context
   ensures  OrigBigfoot(mapThruKlon(os,m),mapThruKlon(context,m))
{
    assert (os <= context);
    assert (forall o <- os ::  o.AMFO <=  context);
    assert OrigBigfoot(os,context);

    reveal m.calid(); assert m.calid();
    reveal m.calidObjects(); assert m.calidObjects();
    reveal m.calidOK(); assert m.calidOK();
    reveal m.calidMap(); assert m.calidMap();
    reveal m.calidSheep(), m.calidSheep2();
    assert m.calidSheep(); 
    assert klonVMapOK(m.m);

assert  (forall x <- m.m.Keys ::
  (set oo <- x.AMFO :: m.m[oo]) == m.m[x].AMFO); //NEW BIT


   assert os <= m.m.Keys;
   assert os <= m.m.Keys  ;
   assert context <= m.m.Keys;
   assert context <= m.m.Keys  ;
   assert os <= context;
   assert OrigBigfoot(os,context);


assert (forall o <- os :: o.AMFO <=  context);

   assert mapThruKlon(os, m) <=  mapThruKlon(context, m);
   assert m.calid();


BothSidesNow(m.m);
MapThruMapPreservesSubsets(os, context, m);
MapThruMapPreservesAMFO(os, context, m);

forall o <- os ensures (
      mapThruKlon(o.AMFO, m) <= mapThruKlon(context, m))
    {
      assert o.AMFO <= context;
      MapThruMapPreservesSubsets(o.AMFO, context, m);
      assert mapThruKlon(o.AMFO, m) == m.m[o].AMFO;
    }


forall r <- mapThruKlon(os, m) ensures (
      r.AMFO <= mapThruKlon(context, m)) {
         MapThruMapPreservesSubsets(os, context, m);
         MapThruMapPreservesAMFO(os, context, m);
         assert r.AMFO <= mapThruKlon(context, m);
      }

   assert (forall o <- mapThruKlon(os, m)  ::  o.AMFO <=   mapThruKlon(context, m)); 


assert  OrigBigfoot(mapThruKlon(os,m),mapThruKlon(context,m));

}




































/////     /////     /////     /////     /////     /////     /////
    /////     /////     /////     /////     /////     /////     /////
/////     /////     /////     /////     /////     /////     /////
    /////     /////     /////     /////     /////     /////     /////