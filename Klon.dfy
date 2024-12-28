//future refactoring TODOs
// oHeap -> contest
// o -> pivot
// o -> ?? nuOwner
// shoiuld klon(c') functions become fgunctiosn on Klon?

function klonKV(c' : Klon, k : Object, v : Object) : (c : Klon)
//extends klon mapping with k:=v
//  requires klonVMapOK(c'.m)
  requires klonCanKV(c', k, v) //klonSatanKV(c', k, v)zz

  ensures  c == c'.(ns := c'.ns + nu(k,v)).(m:= VMapKV(c'.m,k,v))
  ensures  klonVMapOK(c.m)
  ensures  (forall x <- c'.m.Keys :: c.m[x] == c'.m[x])
  ensures  c.m[k] == v
  ensures  (forall x <- c.m.Keys :: c.m[x] ==
              if (x == k) then (v) else (c.m[x]))
//  ensures  c'.calid() ==> c.calid() //presenvation of calidity
  //abstraction inversion
  reads c'.m.Values`fieldModes
  reads c'.m.Keys`fieldModes
  reads k`fields, k`fieldModes
  reads v`fields, v`fieldModes
  reads c'.oHeap`fields, c'.oHeap`fieldModes
  reads c'.ns`fields, c'.ns`fieldModes
  //reads c'.o`fields, c'.o`fieldModes

{

   assert  klonVMapOK(c'.m);

   var c'' := c'.(m:= VMapKV(c'.m,k,v));
   var nsv := (c''.ns + nu(k,v));
   var c   := c''.(ns:= nsv);

assert (forall k <-  c'.m.Keys :: k.AMFO <= c'.m.Keys);

assert k.AMFO <= c'.m.Keys + {k};

   assert  klonVMapOK(c.m);

   c
}

predicate klonSatanKV(c' : Klon, k : Object, v : Object)
//extending c' with k:=v will be klonVMapOK
// requires klonVMapOK(c'.m)  //should this be here?  if not, in below!  //BOWIE
reads c'.m.Values`fieldModes
reads c'.m.Keys`fieldModes
reads k`fieldModes, v`fieldModes
reads c'.oHeap`fields, c'.oHeap`fieldModes
reads c'.ns`fields, c'.ns`fieldModes
reads k`fields, v`fields
{
  //SATAN!!
  //DO NOT DO THIS EVAL.  IT'S HORRIBLE
  //YUCK YUCK YUCK - 202 errors is that a good idea NO!!
  //should this even be HERE?
//   requires
//
    && canVMapKV(c'.m, k, v)
    && (
     var c'' := c'.(m:= VMapKV(c'.m,k,v));
     var nsv := (c''.ns + nu(k,v));
     var c   := c''.(ns:= nsv);

     klonVMapOK(c.m)
    )
//   //SATAN!!
}

predicate klonCanKV(c' : Klon, k : Object, v : Object)
//extending c' with k:=v will be klonVMapOK
// requires klonVMapOK(c'.m)  //should this be here?  if not, in below!  //BOWIE


reads k`fields, k`fieldModes
reads v`fields, v`fieldModes
reads c'.oHeap`fields, c'.oHeap`fieldModes
reads c'.ns`fields, c'.ns`fieldModes
// reads c'.o`fields, c'.o`fieldModes

reads c'.m.Values`fieldModes
reads c'.m.Keys`fieldModes



{
  var ks := c'.m.Keys+{k};



  && klonVMapOK(c'.m) //BOWIE

  && canVMapKV(c'.m, k, v)
  && (k in c'.oHeap)  //KJX do I want this here?
  && (if (v==k) then (v in c'.oHeap) else (v !in c'.oHeap)) //nope - happens after  wards

  && c'.boundsNestingOK(k, c'.oHeap)
  && c'.boundsNestingOK(v, c'.oHeap+c'.ns+{v})

  && c'.boundsNestingOK(k, c'.m.Keys+{k})

//   && c'.fieldMappingsOK(k, v, c'.m.Keys+{k})

// // START DOOUBLE BOWIE
//   && (forall x <-  c'.m.Keys :: x.bound <= x.owner <= c'.m.Keys) //from klonVMapOK
//   && (k.bound <= k.owner <= ks)
//   && (forall x <- ks :: x.bound <= x.owner <= ks)
//
//   && (mapThruVMapKV(k.owner, c'.m, k, v) == v.owner) //KJXOWNERS
//   && (k.AMFO <= ks)
//   && (mapThruVMapKV(k.AMFO, c'.m, k, v) == v.AMFO)
//
//   && (k.bound <= ks)
//   && (mapThruVMapKV(k.bound, c'.m, k, v) == v.bound) //KJXOWNERS
//   && (k.AMFB <= ks)
//   && (mapThruVMapKV(k.AMFB, c'.m, k, v) == v.AMFB)
//
  && (k.fieldModes == v.fieldModes)

  && (v.AMFO >= v.AMFB >= k.AMFB)

//END DOOUBLE BOWIE
}

// lemma SatanCan1(c' : Klon, k : Object, v : Object)
//   requires klonSatanKV(c', k, v)
//   ensures  klonCanKV(c', k, v)
//   {}

// lemma SatanCan2(c' : Klon, k : Object, v : Object)
//   requires klonCanKV(c', k, v)
//   ensures  klonSatanKV(c', k, v)
//   {}



// lemma KlonklonCanKV(c' : Klon, k : Object, v : Object, c : Klon)
// //what's the point of this? does it evcen HAVE a point?
// //SURE - this says - IF you have a calid Klon,
// //and you extend it such that klonCan(c,k,v)
// //THEN the resulting Klon (KlonKV(c,k,v)is also calid
//     requires c'.calid()
//     requires klonCanKV(c',k,v)
//     requires c == klonKV(c',k,v)
//
//     requires k in c'.oHeap
//     requires COK(k, c'.oHeap)
//     requires (v==k) ==> v in c'.oHeap
//     requires (v==k) ==> (COK(v,c'.oHeap))
//     requires (v!=k) ==> (COK(v,c'.oHeap+c'.ns+{v}))
//
//     requires (v==k) == (outside(k, c'.o))
//
//     ensures c.calid()
// {
//   klonCalidKVCalid(c',k,v,c);
// }


lemma IHasKlonVMapOK(m : vmap<Object,Object>, ks : set<Object> := m.Keys)
  requires ks <= m.Keys

//CUT AND PASTE THE BELOW FROM klonVMapOK!!!///
  requires (forall k <- ks :: k.AMFO <= m.Keys)
  // requires (forall k <- ks :: mapThruVMap(k.AMFO, m) == m[k].AMFO)
  requires (forall k <- ks :: k.AMFB <= m.Keys)
  // requires (forall k <- ks :: mapThruVMap(k.AMFB, m) == m[k].AMFB)
  requires (forall x <- ks :: x.owner <= m.Keys)
  requires (forall x <- ks :: x.bound <= m.Keys)
  requires (forall k <- ks :: k.owner <= m.Keys)
  // requires (forall k <- ks :: mapThruVMap(k.owner, m) == m[k].owner)
  requires (forall k <- ks :: k.fieldModes == m[k].fieldModes)

  requires (forall x <- ks :: x.bound <= x.owner <= m.Keys)
  // requires (forall k <- ks :: mapThruVMap(k.bound, m) == m[k].bound)


  ensures klonVMapOK(m,ks)
{
//  assert klonVMapOK(m,ks);
}

predicate   klonVMapOK(m : vmap<Object,Object>, ks : set<Object> := m.Keys)
  requires ks <= m.Keys
//klonVMapOK the vmap parts of a klon are OK
//still need to do something for iHeap and ns etc
//should probably swizzle this to take a Klon, not a vmap/...
//KJX AND that shoud something like klonReady
//meaning that for all targets (m.Keys)
//the coresponding klon  m[k] is
// - ready
// - corresponds to the target
//structure of this needs TO MATCH THE CALIDs and
//object invairants ready, valid, calid, etc
//
// IDEALLY the "mapThru" features shouldn't be part of
// the invariuant itself (klonOK) NOR the extension test (klonCanKV)
// no the extension (klonKC)
// rather mapThru etc should be post-derivable efrom calid, not wired in...
//  which hopefully is ONE clause per "field" of Dahlia's "Object" and no more?
    reads m.Values`fieldModes
    reads ks`fieldModes
{
//AMFO
  && (forall k <- ks :: k.AMFO <= m.Keys)
//  && (forall k <- ks :: mapThruVMap(k.AMFO, m) == m[k].AMFO)

//AMFB
  && (forall k <- ks :: k.AMFB <= m.Keys)
//  && (forall k <- ks :: mapThruVMap(k.AMFB, m) == m[k].AMFB)

//KJXOWNERS
//region & owners?
//  && (forall x <- ks :: x.owner <= x.AMFO)//KJXOWNERS
  && (forall x <- ks :: x.bound <= x.owner <= m.Keys) //should that bound be ks?
//  && (forall k <- ks :: mapThruVMap(k.owner, m) == m[k].owner)
//  && (forall k <- ks :: mapThruVMap(k.bound, m) == m[k].bound)

//field values? //KJX
  && (forall k <- ks :: k.fieldModes == m[k].fieldModes)
}

lemma KlonKVVMapOK(m0 : Klon, k : Object, v : Object, m1 : Klon)
  requires klonVMapOK(m0.m)
  requires klonCanKV(m0, k,  v)
  requires m1 == klonKV(m0, k, v)
  ensures klonVMapOK(m1.m)
  {
    reveal m0.calid(), m0.calidObjects(), m0.calidOK(), m0.calidMap(), m0.calidSheep();
  }


lemma klonCalidKVCalid(m0 : Klon, k : Object, v : Object, m1 : Klon)
  requires klonAllRefsOK(m0)
  requires m0.calid()
  requires MFUCKING: m0.calid()
  requires klonVMapOK(m0.m)
  requires klonCanKV(m0, k, v)

  requires k in m0.oHeap
  requires COK(k, m0.oHeap)
  requires (v==k) ==> v in m0.oHeap
  requires (v==k) ==> (COK(v,m0.oHeap))
  requires (v!=k) ==> (COK(v,m0.oHeap+m0.ns+{v}))


  requires m1 == klonKV(m0, k, v)

  requires (v==k) == (outside(k, m0.o))

  requires (v!=k) ==> (v.fields == map[]) //KJX FRI20DEC - new objects being added need to be empty?

  ensures klonVMapOK(m1.m)
  ensures klonAllRefsOK(m1)
  ensures m1.calid()
  {
        reveal m0.calid(), m0.calidObjects(), m0.calidOK(), m0.calidMap(), m0.calidSheep();
        KlonKVVMapOK(m0, k, v, m1);
IHasCalidMap(m0);


  assert m1 == klonKV(m0, k, v);
  assert (forall x <- m0.m.Keys :: (m1.m[x] == m0.m[x]));


  //calidObiects
        assert m0.ns !! m0.oHeap;
        assert (v==k) ==> v in m0.oHeap;
        assert m1.oHeap == m0.oHeap;
        assert m1.ns == (m0.ns + nu(k,v));
        assert m1.ns !! m0.oHeap;

        assert
            && (m1.o in m1.oHeap)
            && (m1.m.Keys <= m1.oHeap)
            && (m1.ns !! m1.oHeap)
            && (m1.m.Values <= m1.ns + m1.oHeap)
            && (m1.ns <= m1.m.Values)
            ;
        assert m1.calidObjects();


//calidOK
        assert
            && (m1.o in m1.oHeap)
            && (m1.m.Keys <= m1.oHeap)
            && (m1.m.Values <= m1.oHeap+m1.ns)
            && COK(m1.o, m1.oHeap)
            && CallOK(m1.oHeap);

      CallOKfromCOK(k,m0.oHeap);
      CallOKWiderFocus(m0.m.Keys, {k}, m0.oHeap);
      assert CallOK(m1.m.Keys, m1.oHeap);


  assert (v !in m0.ns);
  assert (v==k) ==> (COK(v,m0.oHeap));
  assert (v!=k) ==> (COK(v,m0.oHeap+m0.ns+{v}));

      assert CallOK(m0.m.Values, m0.oHeap+m0.ns);

if (v == k)  {
   assert v in m0.oHeap;
   assert m1 == klonKV(m0,k,v);
   assert m1.oHeap == m0.oHeap;
   assert m1.ns == m0.ns;
   assert v in m1.oHeap;

   assert CallOK(m0.ns, m0.oHeap+m0.ns);
   assert CallOK(m1.ns, m1.oHeap+m1.ns);   //cos ==

   assert (COK(v,m1.oHeap));
   CallOKfromCOK(v,m1.oHeap);
   assert CallOK({v},m1.oHeap);
   CallOKWiderContext({v},m1.oHeap,m1.ns);
   assert CallOK({v},m1.oHeap+m1.ns);

   assert CallOK(m0.m.Values, m0.oHeap+m0.ns);
   assert CallOK(m0.m.Values, m1.oHeap+m1.ns);   //cos ==
   CallOKWiderFocus(m0.m.Values,{v},m1.oHeap+m1.ns);
   assert CallOK(m0.m.Values+{v}, m1.oHeap+m1.ns);
   assert m1.m.Values == m0.m.Values + {v};
   assert CallOK(m1.m.Values, m1.oHeap+m1.ns);

    // assert klonAllOwnersAreCompatible(m0);
    // klonOldOwnersAreStillCompatible(m0,m1);

    klonSameOwnersAreCompatible(k,v,m1);

    assert klonAllOwnersAreCompatible(m1);
    assert klonAllRefsOK(m0);

assert wexford(m0);
// wexfordKV(k,v,m0,m1);
assert wexford(m1);

//    klonAllRefsKVOK(k,v,m0,m1);

    assert klonAllRefsOK(m1);



} else {
   assert v != k;
   assert m1 == klonKV(m0,k,v);
   assert m1.oHeap == m0.oHeap;
   assert m1.ns == m0.ns+{v};
   assert v in m1.ns;

   assert (COK(v, m0.oHeap+m0.ns+{v}));
   assert m0.oHeap+m0.ns+{v}   ==  m0.oHeap+(m0.ns+{v});
   assert m0.oHeap+(m0.ns+{v}) ==  m1.oHeap+m1.ns;
   assert COK(v, m1.oHeap+m1.ns);
   CallOKfromCOK(v,m1.oHeap+m1.ns);
   assert CallOK({v},m1.oHeap+m1.ns);

   assert CallOK(m0.ns, m0.oHeap+m0.ns);
   CallOKWiderContext(m0.ns, m0.oHeap+m0.ns, {v});
   assert CallOK(m0.ns, m0.oHeap+m0.ns+{v});
   assert m0.oHeap+m0.ns+{v}   ==  m0.oHeap+(m0.ns+{v});
   assert m0.oHeap+(m0.ns+{v}) ==  m1.oHeap+m1.ns;
   assert CallOK(m0.ns, m1.oHeap+m1.ns);
   CallOKWiderFocus(m0.ns,{v},m1.oHeap+m1.ns);
   assert CallOK(m0.ns+{v}, m1.oHeap+m1.ns);
   assert CallOK(m1.ns, m1.oHeap+m1.ns);


   assert CallOK(m0.m.Values, m0.oHeap+m0.ns);
   assert CallOK(m0.m.Values, m1.oHeap+m0.ns);  //not the same.
   CallOKWiderContext(m0.m.Values, m1.oHeap+m0.ns, {v});
   assert CallOK(m0.m.Values, m1.oHeap+m0.ns+{v});
   assert CallOK(m0.m.Values, m1.oHeap+(m0.ns+{v}));
   assert m0.ns+{v} == m1.ns;
   assert CallOK(m0.m.Values, m1.oHeap+m1.ns);

   CallOKWiderFocus(m0.m.Values,{v},m1.oHeap+m1.ns);
   assert CallOK(m0.m.Values+{v}, m1.oHeap+m1.ns);
   assert m1.m.Values == m0.m.Values + {v};
   assert CallOK(m1.m.Values, m1.oHeap+m1.ns);


assert v.fields == map[];
    assert klonAllOwnersAreCompatible(m0);
    assert klonOwnersAreCompatible(k,v,m1);

assert forall o <- m0.m.Keys :: klonOwnersAreCompatible(o,m0.m[o],m0);
  assert k !in m0.m.Keys;
assert forall o <- m0.m.Keys :: m1.m[o] == m0.m[o];
assert m0.m.Keys == m1.m.Keys - {k};
assert forall o <- m0.m.Keys :: klonOwnersAreCompatible(o,m1.m[o],m0);

assert forall o <-(m1.m.Keys - {k}):: klonOwnersAreCompatible(o,m1.m[o],m0);


//TODO  -  NEED EXISTENTIONALITY for both k==v and k!=v
//can't do it this way cos of CALIDituty

    assert m1.m == m0.m[k:=v];

    //assert klonAllOwnersAreCompatible(m1);

    assert klonAllRefsOK(m0);

assert wexford(m0);
//wexfordKV(k,v,m0,m1);
assert wexford(m1);



    klonAllRefsKVOK(k,v,m0,m1);

    assert klonAllRefsOK(m1);


   }//end case v != k

      assert CallOK(m1.m.Values, m1.oHeap+m1.ns);
      assert CallOK(m1.ns, m1.oHeap+m1.ns);

        assert m1.calidOK();

//calidMap
assert
    && AllMapEntriesAreUnique(m1.m)
    && klonVMapOK(m1.m) // potentiall should expand this out?
    // && (forall x <- m1.m.Keys, oo <- x.AMFO :: m1.m[oo] in m1.m[x].AMFO)
    // && (forall x <- m1.m.Keys, oo <- x.AMFB :: m1.m[oo] in m1.m[x].AMFB)
;

assert (forall x <- m0.m.Keys :: (not(inside(x,m0.o)) ==> (m0.m[x] == x)));
assert m1.o == m0.o;
assert (forall x <- m0.m.Keys :: (m1.m[x] == m0.m[x]));
assert (forall x <- m0.m.Keys :: (not(inside(x,m1.o)) ==> (m1.m[x] == x)));
assert m1.m[k] == v;
assert m1.m.Keys == m0.m.Keys + {k};
assert m1.o == m0.o;
assert (forall x <- m1.m.Keys :: m1.m[x] == (
         if (x in m0.m.Keys)
           then (assert (m1.m[x] == m0.m[x]); (m0.m[x]))
           else (assert x == k; assert (outside(x,m0.o)) ==> (m1.m[x] == x == k == v); (m1.m[x]))));

assert forall x <- m1.m.Keys :: (not(inside(x,m1.o)) ==> (m1.m[x] == x));

//assert forall x <- m0.m.Keys, oo <- x.owner :: m0.m[oo] in m0.m[x].owner;
assert m1.m[k] == v;
// assert forall oo <- k.owner :: m1.m[oo] in v.owner;
// assert forall x <- m1.m.Keys, oo <- x.owner :: m1.m[oo] in m1.m[x].owner;
// assert forall x <- m1.m.Keys, oo <- x.AMFO :: m1.m[oo] in m1.m[x].AMFO;
IHasCalidMap(m0);
assert (forall x <- m0.m.Keys ::
        && m0.boundsNestingOK(x, m0.oHeap)
        && m0.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns)
        && m0.fieldMappingsOK(x, m0.m[x], m0.m.Keys));

assert
        && m0.boundsNestingOK(k, m0.oHeap)
        && m0.boundsNestingOK(v, m0.oHeap+m0.ns+{v})
        && m0.fieldMappingsOK(k, v, m0.m.Keys+{k});

assert m1.m[k]        == v;
assert m1.m.Keys      == m0.m.Keys + {k};
assert m1.m.Values    == m0.m.Values+{v};
assert m1.oHeap       == m0.oHeap;
assert m1.oHeap+m1.ns == m0.oHeap+m0.ns+{v};
assert m1.o           == m0.o;
assert m1.m[k] == v;

assert
        && m1.boundsNestingOK(k, m1.oHeap)
        && m1.boundsNestingOK(m1.m[k], m1.oHeap+m1.ns)
        && m1.fieldMappingsOK(k, m1.m[k], m1.m.Keys);

  assert m1.calidOK();
  assert m1.calidObjects();
  assert AllMapEntriesAreUnique(m1.m);
  assert klonVMapOK(m1.m);
  assert (forall x <- m1.m.Keys :: (not(inside(x,m1.o)) ==> (m1.m[x] == x)));

assert (forall x <- m0.m.Keys ::
        && m1.boundsNestingOK(x, m0.oHeap)
        && m1.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns)
        && m1.fieldMappingsOK(x, m0.m[x], m0.m.Keys));

  assert (forall x <- m0.m.Keys :: m1.m[x] == m0.m[x]);

//  m1.widerBoundsNest(v,m0.oHeap+m0.ns, m0.oHeap+m0.ns+{v});
  assert (forall x <- m0.m.Keys :: (m0.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns)));
  assert (forall x <- m0.m.Keys ::
    && (m0.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns))
    && (m1.m[x] == m0.m[x])
    && (m0.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns)));

  assert 7: (forall x <- m0.m.Keys :: (m1.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns)));

  assert 75: (forall x <- m0.m.Keys ::
     && (m1.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns))
     && COK(m1.m[x], m0.oHeap+m0.ns)
    // && COK(m1.m[x], m0.oHeap+m0.ns+{v})
    // && COK(m1.m[x], m1.oHeap+m1.ns+{v})
  );

forall x | x in m0.m.Keys ensures (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns)) {
      assert m1.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns);
      assert  COK(m1.m[x], m0.oHeap+m0.ns);
      COKWiderContext2(m1.m[x],m0.oHeap+m0.ns,m0.oHeap+m0.ns+{v});
      assert  COK(m1.m[x], m0.oHeap+m0.ns+{v});
      assert m1.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns+{v});
      assert m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns);
}



  assert 8: (forall x <- m0.m.Keys :: (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns)));

//   assert (forall x <- m0.m.Keys :: (m0.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns)));
//   assert (forall x <- m0.m.Keys :: (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns)));
// //
//
//   assert (forall x <- m0.m.Keys :: m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));
//
//   assert (forall x <- m0.m.Keys :: m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));//FUCKED
//   assert (forall x <- (m0.m.Keys+{k}) :: m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));
//   assert (forall x <- m1.m.Keys :: m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));



    IHasCalidMap(m1);
    assert m1.calidMap();  //FUCKA

//calidSheepKV
    reveal m0.AreWeNotMen();
    reveal UniqueMapEntry();
assert
    && (forall x <- m0.m.Keys :: m0.AreWeNotMen(x, m0))
    && (forall x <- m0.m.Keys :: m0.m[x].fieldModes == m1.m[x].fieldModes)
    && AllMapEntriesAreUnique(m0.m);
FORALLAWNMFUCKED(m0,m1);
assert
    && (forall x <- m0.m.Keys :: m1.AreWeNotMen(x, m1))
    && (forall x <- m1.m.Keys :: x.fieldModes ==
          if (x in m0.m.Keys)
              then (m1.m[x].fieldModes)
              else (assert (x == k) && (m1.m[x] == v) && (k.fieldModes == v.fieldModes); v.fieldModes)
       )
    && AllMapEntriesAreUnique(m1.m)
    ;

IHasCalidSheep(m1);
        assert m1.calidSheep();

        assert m1.from(m0);
        assert m1.calid();
  }


datatype Klon = Klon
(
  m : vmap<Object,Object>, // maps from Original to Clone (or non-clone)
//  m.Keys : set<Object>, //m.Keys - set, keys of the mapping   (must be m.Keys, subset of oHeap)
//  m.Values : set<Object>, //m.Values - set, values or the mapping (must be m.Values, subset of oHeap + ns)
  o : Object,  //o - Owner within which the clone is being performaed, in oHeap  // "pivot"
  //    p : Object,  // Owner of the new (target) clone.  needs to be inside the source object's movement

  o_amfo : Owner,             //was o. so the AMFO of o
  c_amfo : Owner,            //epected ownershio of the clone..

  oHeap : set<Object>,  //oHeap - original (sub)heap contianing the object being cloned and all owners and parts
  ns : set<Object> //ns - new objects  (must be !! oHeap,   m.Values <= oHeap + ns
  // fixedflat ; Bool // true - caopy all ther iretxt=       jnj                    i
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
    && mapGEQ(m, prev.m)
    && o     == prev.o
    && oHeap == prev.oHeap
    && ns    >= prev.ns
    && calid()         //should these be requirements?
       //KJX       && prev.calid()   //currently YES because the underlyign thing will require calid and reutnr calid
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
  //what the TRUMP is this doing
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

    reveal UniqueMapEntry();

    assert m.at(k)  == v;  //why is this needed?
    assert m.m[k]   == v;
    assert forall i <- m.m.Keys :: UniqueMapEntry(m.m, i);
    assert k in m.m.Keys;
    assert UniqueMapEntry(m.m, k);

    assert forall i <- m.m.Keys :: (m.m[i] == v) ==> (i == k);

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
    //ghost function because currently defined to use :| p - could just loop or recurse
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

  opaque predicate got(k : Object) : (g : bool)
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
    reads k`fields, k`fieldModes
    reads v`fields, v`fieldModes
    reads ns`fields, ns`fieldModes
    reads m.Values`fieldModes
    reads m.Keys`fieldModes

    requires calid()
    requires klonAllRefsOK(this) //lemma should be able to derive from calid()
    requires klonVMapOK(m) //lemma can derive from calid()

    requires canVMapKV(m,k,v)
    requires klonCanKV(this,k,v)
    requires AreWeNotMen(k, klonKV(this,k,v))

    requires k  in oHeap
    requires k !in m.Keys
    requires v !in oHeap
    requires v !in ns
    requires v !in m.Values
    requires COK(k, oHeap)
    requires COK(v, oHeap+ns+{v})
    requires m.Keys <= oHeap
    requires k.allExternalOwners() <= m.Keys
    requires v.allExternalOwners() <= oHeap+ns //need to hae proceessed all owners first

    requires (k.owner <= m.Keys)
    // requires (mapThruKlon(k.owner, this) == v.owner)
    // requires (mapThruKlonKV(k.AMFO, this, k, v) == v.AMFO)

    requires inside(k, o)
    requires v.fields == map[] //KJX hmm means something...
    requires v.fieldModes == k.fieldModes

    ensures  r == klonKV(this,k,v)
    ensures  klonVMapOK(r.m)
    ensures  klonVMapOK(m)
    //ensures  r == Klon(VMapKV(m,k,v), o, oHeap, ns+{v})

    ensures  v in r.ns
    ensures  k in r.m.Keys && r.m[k] == v
    ensures  COK(v, r.oHeap+r.ns)
    ensures  k in r.m.Keys
    ensures  v in r.m.Values
    ensures  r.m.Values == m.Values + {v}
    ensures  r.m == m[k:=v]
    ensures  mapLEQ(m, r.m)
    ensures  r.calid()
    ensures  r.from(this)
    ensures  AllMapEntriesAreUnique(this.m)
  {


assert (forall x <- oHeap :: (x.Ready() && x.AllOutgoingReferencesWithinThisHeap(oHeap)))
  by {
    reveal calid();
    assert calid();
    reveal calidObjects();
    assert calidObjects();
    reveal calidOK();
    assert calidOK();
  }

    // assert calidMap();
    // reveal calidMap();
    // assert calidSheep();
    // reveal calidSheep();

    // assert klonVMapOK(m);
    // assert CallOK(oHeap);
    // assert COK(k, oHeap);
    // assert COK(v, oHeap+ns+{v});

    // reveal COK();

    // assert AllMapEntriesAreUnique(m);



    // reveal calid(); assert calid();
      var rv := Klon(VMapKV(m,k,v), o, o_amfo, c_amfo, oHeap, ns+{v});
      assert rv == klonKV(this,k,v);

      assert klonVMapOK(rv.m);

      // reveal calidMap(); assert calidMap(); assert klonVMapOK(m);

      // assert klonKV(this,k,v).m == VMapKV(m,k,v) by { reveal calidMap(); assert calidMap(); assert klonVMapOK(m);}
      //assert rv == klonKV(this,k,v);

      assert oXn: oHeap !! ns by { assert calid(); reveal calid();  assert calidObjects(); reveal calidObjects();}

      assert COK(v, rv.oHeap+rv.ns) by {
        var rrr := rv.oHeap+rv.ns;
        var vvv := oHeap+ns+{v};
        assert COK(v, vvv);  // from reqs
        assert rv.oHeap+rv.ns == oHeap+(ns+{v});
        assert rrr == vvv;
        assert COK(v, rrr);
      }

    assert rv.calidObjects() by {
      reveal rv.calidObjects();

      assert rv.o in rv.oHeap by {
        assert calid(); reveal calid();
        assert calidObjects(); reveal calidObjects();
        assert o in oHeap;
        assert rv.o == o;
        assert rv.o in oHeap;
        assert rv.oHeap == oHeap;
        assert rv.o in rv.oHeap;
      }
      assert rv.m.Keys <= rv.oHeap;
      assert rv.ns !! rv.oHeap by {
        assert ns !! oHeap by { reveal oXn; }
        assert v !in oHeap;
        assume {v} !! oHeap;   //why do we need this given the above? - answer: to speed veriication?
        assert (ns + {v}) !! oHeap;
        assert rv.oHeap == oHeap;
        assert (ns + {v}) !! rv.oHeap;
        assert rv.ns == ns+{v};
        assert rv.ns !! rv.oHeap;
      }
      assert m.Values <= ns + oHeap by {
                  assert calid(); reveal calid();
                  reveal calidObjects(); assert calidObjects(); }

      assert ns <= m.Values by {
                  assert calid(); reveal calid();
                  reveal calidObjects(); assert calidObjects(); }
      assert rv.m.Values <= rv.ns + rv.oHeap;
      assert rv.ns <= rv.m.Values;

      assert rv.calidObjects();
    }

    assert v !in m.Values; // from reqs

    assert rv.calidOK() by {
      reveal rv.calidOK();
      reveal rv.calidObjects();
      assert COK(rv.o, rv.oHeap) by {
          assert calid();
          reveal calid();
          assert calidOK();
          reveal calidOK();
          assert COK(o, oHeap);
          assert rv.o == o;
          assert COK(rv.o, oHeap);
          assert rv.oHeap == oHeap;
          assert COK(rv.o, rv.oHeap);
      }
      assert CallOK(rv.oHeap) by {
           assert calid(); reveal calid();
           reveal calidOK(); assert calidOK();
           assert CallOK(oHeap);
           assert rv.oHeap == oHeap;
           assert CallOK(rv.oHeap);
      }

      CallOKfromCOK(k, oHeap);
      assert CallOK(m.Keys, oHeap) by {
           assert calid(); reveal calid();
           reveal calidOK(); assert calidOK();
           assert CallOK(m.Keys, oHeap);
      }
      CallOKtoSubset(m.Keys, oHeap);
      CallOKWiderFocus(m.Keys, {k}, oHeap);
      assert CallOK(rv.m.Keys, rv.oHeap);
      assert oHeap+ns+{v} == rv.oHeap+rv.ns;
      assert COK(v, rv.oHeap+rv.ns);
      // CallOKWiderContext({v}, rv.oHeap, rv.ns);    //unneeded?
      // CallOKtoSubset(rv.m.Values, rv.oHeap+rv.ns);       //unneeded?
      assert rv.m.Values <= rv.ns + oHeap;
      assert CallOK(m.Values, oHeap+ns) by {
           assert calid(); reveal calid();
           reveal calidOK(); assert calidOK();
           assert CallOK(m.Values, oHeap+ns);
      }
      CallOKWiderContext(m.Values, oHeap+ns, {v});
      assert COK(v,oHeap+ns+{v}); //reqs
      CallOKfromCOK(v, oHeap+ns+{v});   //could subsume within COK?> (or not0)
      CallOKWiderFocus(m.Values, {v}, oHeap+ns+{v});  //version just adding one?
      assert m.Values+{v} == rv.m.Values;
      assert CallOK(rv.m.Values, rv.oHeap+rv.ns);
      assert ns+{v} == rv.ns;
      var rrr := rv.oHeap+rv.ns;
      var vvv := oHeap+ns+{v};
      assert COK(v, vvv);  // from reqs
      assert rv.oHeap+rv.ns == oHeap+(ns+{v});
      assert rrr == vvv;
      assert COK(v, rrr);
       assert CallOK(rv.ns, rv.oHeap+rv.ns) by {  //is it worth cobinging these also
           assert calid(); reveal calid();
           reveal calidOK(); assert calidOK();
           assert CallOK(ns,oHeap+ns);
           CallOKWiderContext(ns,oHeap+ns,{v});
           assert CallOK(ns,oHeap+ns+{v});
           assert rv.oHeap+rv.ns == rv.oHeap+rv.ns;
           assert CallOK(ns,rv.oHeap+rv.ns);
           assert COK(v, rv.oHeap+rv.ns);
           CallOKfromCOK(v, rv.oHeap+rv.ns);
           CallOKWiderFocus(ns,{v},rv.oHeap+rv.ns);
           assert ns+{v} == rv.ns;
           assert CallOK(rv.ns, rv.oHeap+rv.ns);
      }
      assert CallOK(rv.ns, rv.oHeap+rv.ns);
        reveal rv.calidOK();
      IHasCalidOK(rv);
      assert rv.calidOK();
    }



      // assert mapThruKlonKV(k.AMFO, this, k, v) == v.AMFO;

     KlonVMapOKfromCalid(this);
     assert klonVMapOK(m);
     assert klonVMapOK(rv.m);


      // assert (forall x <- m.Keys     :: mapThruKlon(x.AMFO, this) == m[x].AMFO);
      // assert (forall x <- m.Keys     :: mapThruKlonKV(x.AMFO, this, k, v) == m[x].AMFO);
      // assert (forall x <- m.Keys+{k} :: mapThruKlonKV(x.AMFO, this, k, v) == m[x].AMFO);
      // assert rv.m.Keys == m.Keys + {k};
      // assert rv == klonKV(this,k,v);
      // assert (forall x <- rv.m.Keys  :: mapThruKlon(x.AMFO, rv)   == rv.m[x].AMFO);

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






    reveal rv.calidObjects();
    assert m.Keys == m.Keys;
    assert rv.m.Keys == rv.m.Keys;

    assert rv.m[k] == v;
    assert v in rv.ns;
    assert inside(k,rv.o);
 //   assert (inside(k,rv.o)) ==> (rv.m[k] in ns);

    assert (forall x <- m.Keys :: AreWeNotMen(x, this))
        by { reveal calid(); assert calid(); reveal calidSheep(); assert calidSheep(); }
    reveal AreWeNotMen();
    assert (forall x <- m.Keys  :: (not(inside(x,o)) ==> (m[x] == x)));
    assert (forall x <- m.Keys  :: (not(inside(x,o)) ==> (rv.m[x] == x)));
    //assert (forall x <- {k} ::     (not(inside(x,o)) ==> (rv.m[x] == x)));
          //above line is contradiction & wrong - we have inside(k,o) && k !in m.Keys ...
    assert (forall x <- m.Keys+{k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
    assert rv.m.Keys == m.Keys + {k};
    assert rv.m.Keys == rv.m.Keys;
    assert (forall x <- rv.m.Keys  :: (not(inside(x,o)) ==> (rv.m[x] == x)));

//do I need these?  why?
    // assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
    // assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);

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

assert klonAllRefsOK(this);
assert calid();
assert klonVMapOK(m);
assert klonCanKV(this, k, v);

assert k in oHeap;
assert COK(k, oHeap);
assert COK(v,oHeap+ns+{v});


klonCalidKVCalid(this, k, v, rv);

  //  IHasCalidMap(rv);
    assert  rv.calidMap() by { reveal calid(); }

    // assert rv.calidMap() by {
    //     reveal rv.calidObjects(); assert rv.calidObjects();
    //     reveal rv.calidOK(); assert rv.calidOK();
    //     assert
    //       && AllMapEntriesAreUnique(rv.m)
    //       && klonVMapOK(rv.m) // potentiall should expand this out?
    //       && (forall x <- rv.m.Keys :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)))
    //       && (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO)
    //       ;
    //     reveal rv.calidMap();
    //     assert rv.calidMap();
    // }

    reveal rv.calidSheep();
    reveal rv.calidObjects();
    assert m.Keys == m.Keys;
    assert rv.m.Keys == rv.m.Keys;
    assert inside(k, o);
  //  reveal calidMap();
  //  assert calidMap() by {
                           assert calid();
                           reveal calid();
                           assert calidObjects();
                           assert calidOK();
                           assert calidMap();
   // }
    reveal calidSheep();


    assert forall x <- m.Keys :: AreWeNotMen(x, this);
    assert rv.m.Keys == rv.m.Keys == (m.Keys+{k});

    assert forall x <- m.Keys :: x.fieldModes == m[x].fieldModes;
    assert k.fieldModes == v.fieldModes;
    assert calidSheep() by {
      reveal calid();
      assert calid();
      assert calidSheep();
    }
    reveal rv.calidSheep();
    //reveal UniqueMapEntry();

    assert m.Keys == m.Keys;

    reveal AreWeNotMen();
    reveal UniqueMapEntry();
    KlonKVExtendsTo(this, k, v, rv);
    assert forall x <- m.Keys  :: AreWeNotMen(x, this);
    assert forall x <- m.Keys  :: (this.m[x] == rv.m[x]);
 // assert forall x <- m.Keys  :: (AreWeNotMen(x, this) ==> AreWeNotMen(x, rv));

  assert klonVMapOK(this.m);
  assert klonCanKV(this, k, v);
  assert rv == klonKV(this, k, v);
//  assert forall x <- this.m.Keys :: AreWeNotMen(x, rv);
  assert AreWeNotMen(k, rv);

    // assert forall x <- m.Keys  :: AreWeNotMen(x, rv);
    // assert forall x <- {k} :: AreWeNotMen(x, rv);
    // assert rv.m.Keys == m.Keys + {k};
    assert forall x <- rv.m.Keys :: AreWeNotMen(x, rv) by
    {
        KlonExtendsDEVO(this, k, v, rv);
    }

    // assert forall x <- m.Keys  :: x.fieldModes == rv.m[x].fieldModes;
    // assert forall x <- {k} :: x.fieldModes == rv.m[x].fieldModes;
    // assert rv.m.Keys == m.Keys + {k};
    // assert forall x <- rv.m.Keys ::
    //       if (x in m.Keys)
    //        then (x.fieldModes == rv.m[x].fieldModes)
    //        else ((x == k) && (x.fieldModes == k.fieldModes == v.fieldModes == rv.m[x].fieldModes));
    // assert forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes;

    KlonKVExtendsTo(this, k, v, rv);
    assert klonVMapOK(rv.m);

    // assert forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes by
    //   {
    //      assert klonVMapOK(this.m);
    //      assert klonCanKV(this, k, v);
    //      KlonExtendsFieldModes(this, k, v, rv);
    //      assert FUKKA(rv);
    //      assert      forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes by
    //        { assert FUKKA(rv);
    //          reveal FUKKA();
    //          assert  forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes;
    //         }
    //    }

    assert FUKKA(rv) by
      {
         assert klonVMapOK(this.m);
         assert klonCanKV(this, k, v);
         KlonExtendsFieldModes(this, k, v, rv);
         assert FUKKA(rv);
      }

    assert rv.calidSheep() by {
        reveal calid(); assert calid();
        reveal calidObjects(); assert calidObjects();
        reveal calidOK(); assert calidOK();

        assert rv.calidObjects();
        assert rv.calidOK();
        assert (forall x <- rv.m.Keys :: AreWeNotMen(x, rv));

        assert FUKKA(rv);
        reveal FUKKA();
        AKKUF(rv);
        assert (forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes);

        // assert (forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes) by
        //   {
        //          assert FUKKA(rv);
        //          AKKUF(rv);
        //          assert (forall x <- rv.m.Keys :: x.fieldModes == rv.m[x].fieldModes);
        //   }
        assert AllMapEntriesAreUnique(rv.m);

          //WHO KNOWS, WHO KNOWS...
        IHasCalidSheep(rv);
        assert rv.calidSheep();
    }
    reveal rv.calid(); assert rv.calid();

    rv
    } //END putInside

//
//
//



lemma foo() {}









opaque predicate FUKKA(d : Klon)
  reads d.m.Keys`fieldModes
  reads d.m.Values`fieldModes
{
  forall x <- d.m.Keys :: x.fieldModes == d.m[x].fieldModes
}


lemma AKKUF(d : Klon)
  requires FUKKA(d)
  ensures  forall x <- d.m.Keys :: x.fieldModes == d.m[x].fieldModes
{
  reveal FUKKA();
  assert FUKKA(d);
}



lemma KlonExtendsFieldModes(c : Klon, k : Object, v : Object, d : Klon)
  requires klonVMapOK(c.m)
  requires klonCanKV(c, k, v)
  requires d == klonKV(c, k, v)
  ensures  klonVMapOK(d.m)
  ensures  forall x <- d.m.Keys :: x.fieldModes == d.m[x].fieldModes
  ensures  FUKKA(d)
{
  reveal FUKKA();
  KlonKVExtendsTo(c, k, v, d);
}


lemma KlonExtendsDEVO(c : Klon, k : Object, v : Object, d : Klon)
  requires klonVMapOK(c.m)
  requires klonCanKV(c, k, v)
  requires d == klonKV(c, k, v)

  requires forall x <- c.m.Keys :: AreWeNotMen(x, c)
  requires AreWeNotMen(k,d)
  ensures  klonVMapOK(d.m)
  ensures  forall x <- d.m.Keys :: AreWeNotMen(x, d)
{
  assert k !in c.m.Keys;
  assert v !in c.m.Values;
  assert forall x <- c.m.Keys :: AreWeNotMen(x, c);
  reveal AreWeNotMen();
  assert forall x <- c.m.Keys ::
    && (c.m[x] == d.m[x])
    && (AreWeNotMen(x, c) == AreWeNotMen(x, d));
  assert forall x <- c.m.Keys :: AreWeNotMen(x, d);

  KlonKVExtendsTo(c, k, v, d);
  assert c.m.Keys + {k} == d.m.Keys;
}



lemma KlonExtendsCalidObjects(c : Klon, k : Object, v : Object, d : Klon)
  requires klonVMapOK(c.m)
  requires klonCanKV(c, k, v)
  requires d == klonKV(c, k, v)
  requires c.calidObjects() || c.calid()

//do I need this lot or just fold in and need only c.calid*()
  requires c.o in c.oHeap
  requires c.m.Keys <= c.oHeap

  requires  (c.ns + nu(k,v)) !! c.oHeap
  ///requires not(theValueIsNew) ==> (v in c.oHeap)
  //can work it out if k==v, we k ow k i n oNHep...

  requires c.m.Values <= c.ns + c.oHeap
  requires c.ns <= c.m.Values

  ensures  d.calidObjects()
{

  if (c.calidObjects()) {
      reveal c.calidObjects();
  } else {
      reveal c.calid();
      assert  {:contradiction} c.calid();
      assert {:contradiction}
        && calidObjects()
        && calidOK()
        && calidMap()
        && calidSheep()
        ;
        assert  {:contradition} c.calidObjects();
      reveal c.calidObjects();
  }

  reveal c.calidObjects();

  assert c.calidObjects();
  assert c.o in c.oHeap;
  assert c.m.Keys <= c.oHeap;
  assert c.ns !! c.oHeap;
  assert c.m.Values <= c.ns + c.oHeap;
  assert c.ns <= c.m.Values;

  assert d.m        == VMapKV(c.m, k, v);
  assert d.m.Keys   == c.m.Keys + {k};
  assert d.m.Values == c.m.Values + {v};
  assert d.ns       == c.ns + nu(k,v);
  assert d.o        == c.o;
  assert d.oHeap    == d.oHeap;


  assert d.o in d.oHeap;
  assert d.m.Keys <= d.oHeap;
  assert d.ns !! d.oHeap;
  assert d.m.Values <= d.ns + d.oHeap;
  assert d.ns <= d.m.Values;

  reveal d.calidObjects();
  assert d.calidObjects();
}



  opaque function putOutside(k : Object) : (r : Klon)
    //put k -> k into map, k oustide o
    reads oHeap`fields, oHeap`fieldModes
    reads k`fields, k`fieldModes
    reads ns`fields, ns`fieldModes
    reads o`fields, o`fieldModes
    reads m.Values`fieldModes
    reads m.Keys

    requires calid()
    requires klonVMapOK(m) //lemma can derive from calid()
    requires klonAllRefsOK(this)

    requires canVMapKV(m,k,k)
    requires klonCanKV(this,k,k)
    requires AreWeNotMen(k, klonKV(this,k,k))

    requires k  in oHeap
    requires k !in m.Keys
    requires k !in m.Values
    requires COK(k, oHeap)
    requires m.Keys <= oHeap
    requires k.allExternalOwners() <= m.Keys

    // requires (k.owner <= m.Keys) && (mapThruKlon(k.owner, this) == k.owner)  //OK right but why require it?
    // requires mapThruKlonKV(k.AMFO, this, k, k) == k.AMFO   //OK right but why require it?

    requires outside(k, o)
    requires forall oo <- k.owner :: outside(oo,o) //see commetns above about "mapThruKlon(k.owner, this) == k.owner"

    ensures r == klonKV(this,k,k)
    ensures  klonVMapOK(r.m)
    ensures  klonVMapOK(m)

    ensures r.calid()
    ensures r.from(this)

  {
    var r := klonKV(this,k,k);

    assert calid();
    reveal calid();
    assert calidObjects();
    reveal calidObjects();
    reveal calidOK();
    assert calidOK();
    reveal calidMap();
    assert calidMap();
    reveal calidSheep();
    assert calidSheep();

    KlonExtendsCalidObjects(this, k, k, r);

    IHasCalidObjects(r);

  assert r.m.Keys == m.Keys + {k};
  assert r.m.Values == m.Values + {k};
  assert r.ns == ns;
  assert r.oHeap == oHeap;

    assert CallOK(m.Keys, oHeap);
    assert COK(k,oHeap);
    CallOKfromCOK(k,oHeap);
    assert CallOK({k},oHeap);
    CallOKWiderFocus(m.Keys,{k},r.oHeap);
    assert CallOK(r.m.Keys, r.oHeap);

    assert CallOK(m.Values, oHeap+ns);
    assert CallOK({k},oHeap);
    CallOKWiderContext({k},oHeap,r.ns);
    assert CallOK({k},r.oHeap+r.ns);
    CallOKWiderFocus(m.Values,{k},r.oHeap+ns);
    assert CallOK(r.m.Values, r.oHeap+r.ns);

    assert CallOK(  ns,   oHeap+  ns);
    assert CallOK(r.ns, r.oHeap+r.ns);
klonCalidKVCalid(this, k, k, r);
    IHasCalidOK(r);
    IHasCalidMap(r);

    assert klonVMapOK(this.m);
    assert klonCanKV(this, k, k);
    assert r == klonKV(this, k, k);

    reveal AreWeNotMen();
    assert forall x <- this.m.Keys :: AreWeNotMen(x, r);
    assert AreWeNotMen(k,r);
    KlonExtendsDEVO(this, k, k, r);

    IHasCalidSheep(r);
    IHasCalid(r);

    r
  }


















































  predicate weirdo()
  //from  calid get klonVMapOK AllMapENtiresAreUNique
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




  opaque predicate AreWeNotMen(x : Object,  rv : Klon)  //hmmm wgt etc?
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires x in rv.m.Keys
  {
    && (   (inside(x,rv.o)) ==> (rv.m[x] in rv.ns))
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


  // static lemma AintNoSunshine2(x : Object, rv : Klon)
  //   //
  //   requires not(inside(x,rv.o))
  //   requires x !in rv.m.Keys

  //   requires rv.calid()
  //   requires forall k <- rv.m.Keys :: rv.AreWeNotMen(k,rv)
  //   requires x  in rv.oHeap
  //   requires x !in rv.ns

  //   ensures  x !in rv.m.Values
  // {
  //   assert rv.calid();

  //   reveal rv.calid();
  //   assert rv.calid();

  //   reveal rv.calidObjects();
  //   assert rv.calidObjects();
  //   reveal rv.calidOK();
  //   assert rv.calidOK();
  //   reveal rv.calidMap();
  //   assert rv.calidMap();
  //   reveal rv.calidSheep();
  //   assert rv.calidSheep();


  //   // forall k <- rv.m.Keys

  // }

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
    reveal rv.AreWeNotMen();
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
  {
    reveal calidObjects();  //why? do I need this??

    && calidObjects()
    && calidOK()
    && calidMap()
    && calidSheep()
  }

  opaque predicate calidObjects()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
  {
    && o in oHeap
    && m.Keys <= oHeap
    && ns !! oHeap
    && m.Values <= ns + oHeap
    && ns <= m.Values
  }

  opaque predicate calidOK()
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

    && forall x <- oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(oHeap)
  }


  opaque predicate calidMap()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calidObjects() && calidOK()
  {
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    reveal CallOK();

    && AllMapEntriesAreUnique(m)
    && klonVMapOK(m) // potentiall should expand this out?

    && (forall x <- m.Keys ::
        && boundsNestingOK(x, oHeap)
        && boundsNestingOK(m[x], oHeap+ns)
        && fieldMappingsOK(x, m[x], m.Keys))

    && klonAllOwnersAreCompatible(this)

  //  && klonAllRefsOK(this)

    && (forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x)))
    // && (forall x <- m.Keys, oo <- x.owner :: m[oo] in m[x].owner) //KJXOWNERS
    // && (forall x <- m.Keys, oo <- x.bound :: m[oo] in m[x].bound) //KJXOWNERS
    // && (forall x <- m.Keys, oo <- x.AMFO  :: m[oo] in m[x].AMFO)
    // && (forall x <- m.Keys, oo <- x.AMFB  :: m[oo] in m[x].AMFB)
  }

  opaque predicate  calidSheep2()
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


  opaque predicate calidSheep()
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires calidObjects() && calidOK()// && calidMap()
  {
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    //reveal calidMap(); assert calidMap();

    reveal AreWeNotMen();
    //reveal UniqueMapEntry();

    && (forall x <- m.Keys :: AreWeNotMen(x, this))
    && (forall x <- m.Keys :: x.fieldModes == m[x].fieldModes)
    && AllMapEntriesAreUnique(m)
  }



  opaque predicate calidSheep3()
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





  lemma sheep12()
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


lemma calidOKFromCalid()
  //reveals m.calidOK pretty much
  //KJX shoiuld this be  here our external or?
  requires calid()
  ensures  (o in oHeap)
  ensures  (m.Keys <= oHeap)
  ensures  (m.Values <= oHeap+ns)
  ensures  COK(o, oHeap)
  ensures  CallOK(oHeap)
  ensures  CallOK(m.Keys, oHeap)
  ensures  CallOK(m.Values, oHeap+ns)
  ensures  CallOK(ns, oHeap+ns)
{
  reveal calid();
  reveal calidOK();
}



// lemma NewObjectMapppings(k : Object, v : Object, context : set<Object>)
//     ensures owner == oo
//     ensures AMFO == flattenAMFOs(oo) + {this}
//     ensures bound == mb
//     ensures AMFB == flattenAMFOs(mb) + {this}  //HMM dunno if "this" should be here, but...
// {}


predicate fieldMappingsOK(k : Object, v : Object, context : set<Object>)
  //  reads k, v, context
  // reads k`fields, k`fieldModes
  // reads v`fields, v`fieldModes
  // reads oHeap`fields, oHeap`fieldModes
  // reads ns`fields, ns`fieldModes
  // reads o`fields, o`fieldModes
{
  true
}

//     && COK(k,oHeap)     //>>> Do I want?)
//     && COK(v,oHeap+ns)  //>>> Do I want?)
//     && ((not(inside(k,o)) ==> (k == v)))
//
//     && boundsNestingOK(k, m.Keys)  /// or "contect"
//     && boundsNestingOK(v, oHeap+ns)
//
//     && (o.allExternalOwners() <= m.Keys)
//
//     && ((set x <- k.owner :: m[x]) == v.owner)
//     && ((set x <- k.bound :: m[x]) == v.bound)
//     && ((set x <- k.AMFO  :: m[x]) == v.AMFO)
//     && ((set x <- k.AMFB  :: m[x]) == v.AMFB)




//YOUR MEN ARE ALREADY DEAD.
//YOUR MEN ARE ALREADY DEAD.
//YOUR MEN ARE ALREADY DEAD.



//     && (mapThruKlon(k.owner, this) == v.owner)
//     && (mapThruKlon(k.bound, this) == v.bound)
//     && (mapThruKlon(k.AMFO,  this) == v.AMFO)
//     && (mapThruKlon(k.AMFB,  this) == v.AMFB)

    // && (forall oo <- k.owner :: m[oo] in v.owner) //KJXOWNERS
    // && (forall oo <- k.bound :: m[oo] in v.bound) //KJXOWNERS
    // && (forall oo <- k.AMFO  :: m[oo] in v.AMFO)
//     // && (forall oo <- k.AMFB  :: m[oo] in v.AMFB)
//
//     && k.fieldModes == v.fieldModes
//
// }

predicate boundsNestingOK(o : Object, context : set<Object>)
  reads oHeap`fields, oHeap`fieldModes
  reads ns`fields, ns`fieldModes
  reads o`fields, o`fieldModes
  //requires COK(o, context)
  {
  && COK(o, context)
  && ownerInsideOwner(o.owner, o.bound)
  && ownerInsideOwner(o.AMFO, o.AMFB)
  && ownerInsideOwner(o.AMFB, o.bound)
  && ownerInsideOwner(o.AMFO, o.bound)
  && ownerInsideOwnerInsideOwner(context, o.owner, o.bound)
  && ownerInsideOwnerInsideOwner(context, o.AMFO, o.AMFB)
  && ownerInsideOwner(o.allExternalOwners(),o.allExternalBounds())
  && ownerInsideOwnerInsideOwner(o.AMFO,o.allExternalOwners(),o.owner)
  }

lemma boundsNestingFromCalid(o : Object, context : set<Object>)
  requires calid()
  requires COK(o, context)

  ensures  boundsNestingOK(o, context)

  ensures  ownerInsideOwner(o.owner, o.bound)
  ensures  ownerInsideOwner(o.AMFO, o.AMFB)
  ensures  ownerInsideOwner(o.AMFB, o.bound)
  ensures  ownerInsideOwner(o.AMFO, o.bound)
  ensures  ownerInsideOwnerInsideOwner(context, o.owner, o.bound)
  ensures  ownerInsideOwnerInsideOwner(context, o.AMFO, o.AMFB)
  ensures  ownerInsideOwner(o.allExternalOwners(),o.allExternalBounds())
  ensures  ownerInsideOwner(o.AMFO,o.allExternalOwners())
  ensures  ownerInsideOwner(o.AMFB,o.allExternalBounds())
  {
    reveal calid(); assert calid();
    reveal calidObjects(); assert calidObjects();
    reveal calidOK(); assert calidOK();
    reveal calidMap(); assert calidMap();
    reveal calidSheep(), calidSheep2();
    assert calidSheep();
    reveal COK();

    assert  ownerInsideOwner(o.owner, o.bound);
    assert  ownerInsideOwner(o.AMFO, o.AMFB);
    assert  ownerInsideOwner(o.AMFB, o.bound);
    assert  ownerInsideOwner(o.AMFO, o.bound);
    assert  ownerInsideOwnerInsideOwner(context, o.owner, o.bound);
    assert  ownerInsideOwnerInsideOwner(context, o.AMFO, o.AMFB);
    assert  ownerInsideOwner(o.allExternalOwners(),o.allExternalBounds());
    assert  ownerInsideOwner(o.AMFO,o.allExternalOwners());
    assert  ownerInsideOwner(o.AMFB,o.allExternalBounds());
  }

lemma widerBoundsNest(o : Object, less : set<Object>, more : set<Object>)
  requires less <= more
  requires boundsNestingOK(o,less)
  ensures  boundsNestingOK(o,more)
  {
    assert COK(o, less);
    COKWiderContext2(o, less, more);
    assert COK(o, more);

  }



//shoudl this be in another file?
//should this talk about KLON?
method COKput(f : Object, context : set<Object>, n : string, t : Object)
  requires COK(f, context)
  requires n  in f.fieldModes.Keys
  requires n !in f.fields.Keys
  requires COK(t, context)
  requires refOK(f, t)
  requires AssignmentCompatible(f, f.fieldModes[n], t)
  ensures  n in f.fields.Keys
  ensures  f.fields[n] == t
//  ensures  forall x <- old(f.fields.Keys) :: f.fields[x] == old(f.fields[x])\
  ensures f.fields == old(f.fields)[n:=t]
  ensures  COK(f, context)
  modifies f`fields
{
  reveal COK();
var a := f;
assert
      && (a in context)
    && (a.AMFO <= context)
    && (forall oo <- a.AMFO :: oo.Ready())
  //  && (a.TRUMP()||(a.Ready() && a.Valid()))
    && (a.Ready())
    && (a.Valid())
    && (a.AllOutgoingReferencesAreOwnership(context))
//    && (a.AllOutgoingReferencesWithinThisHeap(context))
    && (a.AllOwnersAreWithinThisHeap(context))

    && AllTheseOwnersAreFlatOK(a.AMFO - {a})
    ;
  f.fields := f.fields[n:=t];

assert
      && (a in context)
    && (a.AMFO <= context)
    && (forall oo <- a.AMFO :: oo.Ready())
  //  && (a.TRUMP()||(a.Ready() && a.Valid()))
    && (a.Ready())
    && (a.Valid())
    && (a.AllOutgoingReferencesAreOwnership(context))
  //  && (a.AllOutgoingReferencesWithinThisHeap(context))
    && (a.AllOwnersAreWithinThisHeap(context))

    && AllTheseOwnersAreFlatOK(a.AMFO - {a})
    ;


}


  opaque function putin(k : Object, v : Object) : (r : Klon)
    //put k -> v into map, k inside o
    reads oHeap`fields, oHeap`fieldModes
    reads k`fields, k`fieldModes
    reads v`fields, v`fieldModes
    reads ns`fields, ns`fieldModes

//     requires calid()
//     requires klonVMapOK(m) //lemma can derive from calid()
//
       requires canVMapKV(m,k,v)
//     requires klonCanKV(this,k,v)
//     requires AreWeNotMen(k, klonKV(this,k,v))
//
//     requires k  in oHeap
//     requires k !in m.Keys
//     requires v !in oHeap
//     requires v !in ns
//     requires v !in m.Values
//     requires COK(k, oHeap)
//     requires COK(v, oHeap+ns+{v})
//     requires m.Keys <= oHeap
//     requires k.allExternalOwners() <= m.Keys
//     requires v.allExternalOwners() <= oHeap+ns //need to hae proceessed all owners first ************
//
//     requires (k.owner <= m.Keys) && (mapThruKlon(k.owner, this) == v.owner)
//     requires mapThruKlonKV(k.AMFO, this, k, v) == v.AMFO
//
//     requires inside(k, o)
//     requires v.fieldModes == k.fieldModes
//
//     ensures  r == klonKV(this,k,v)
//     ensures  klonVMapOK(r.m)
//     ensures  klonVMapOK(m)
//     //ensures  r == Klon(VMapKV(m,k,v), o, oHeap, ns+{v})
//
//     ensures  v in r.ns
//     ensures  k in r.m.Keys && r.m[k] == v
//     ensures  COK(v, r.oHeap+r.ns)
    ensures  k in r.m.Keys
    ensures  v in r.m.Values
    ensures  r.m == m[k:=v]
    ensures  mapLEQ(m, r.m)

  ensures  mapLEQ(m,r.m)
  ensures  r.m.Keys >= m.Keys + {k}
//   ensures  m.m.Values >= m'.m.Values + {b}
  ensures  r.o == o
  ensures  r.oHeap == oHeap

//     ensures  r.calid()
//     ensures  r.from(this)
    // ensures  AllMapEntriesAreUnique(this.m)
  {
    var rv := Klon(VMapKV(m,k,v), o, o_amfo, c_amfo, oHeap, ns+{v});
    rv
    } //END putin


  opaque function putout(k : Object) : (r : Klon)
    //put k -> v into map, k inside o
    reads oHeap`fields, oHeap`fieldModes
    reads k`fields, k`fieldModes
    reads ns`fields, ns`fieldModes

//     requires calid()
//     requires klonVMapOK(m) //lemma can derive from calid()
//
       requires canVMapKV(m,k,k)
//     requires klonCanKV(this,k,v)
//     requires AreWeNotMen(k, klonKV(this,k,v))
//
//     requires k  in oHeap
//     requires k !in m.Keys
//     requires v !in oHeap
//     requires v !in ns
//     requires v !in m.Values
//     requires COK(k, oHeap)
//     requires COK(v, oHeap+ns+{v})
//     requires m.Keys <= oHeap
//     requires k.allExternalOwners() <= m.Keys
//     requires v.allExternalOwners() <= oHeap+ns //need to hae proceessed all owners first
//
//     requires (k.owner <= m.Keys) && (mapThruKlon(k.owner, this) == v.owner)
//     requires mapThruKlonKV(k.AMFO, this, k, v) == v.AMFO
//
//     requires inside(k, o)
//     requires v.fieldModes == k.fieldModes
//
    // ensures  r == klonKV(this,k,k)
    // ensures  klonVMapOK(r.m)
    // ensures  klonVMapOK(m)
    ensures  r == Klon(VMapKV(m,k,k), o, o_amfo, c_amfo, oHeap, ns)

//     ensures  v in r.ns
    ensures  k in r.m.Keys && r.m[k] == k

    ensures  k in r.m.Values
    ensures  r.m == m[k:=k]
    ensures  mapLEQ(m, r.m)
//     ensures  COK(v, r.oHeap+r.ns)
//     ensures  k in r.m.Keys
//     ensures  v in r.m.Values
//     ensures  r.m == m[k:=v]
//     ensures  mapLEQ(m, r.m)
//     ensures  r.calid()
//     ensures  r.from(this)
    // ensures  AllMapEntriesAreUnique(this.m)
  {
    var rv := Klon(VMapKV(m,k,k), o, o_amfo, c_amfo, oHeap, ns);
    rv
    } //END putout



} ///end datatype Klon

lemma AWNMFUCKED(x : Object,  rv : Klon, other : Klon)
  requires x in rv.m.Keys
  requires rv.AreWeNotMen(x,rv)
  ensures  other.AreWeNotMen(x,rv)
  {
    reveal rv.AreWeNotMen();
    assert other.AreWeNotMen(x,rv);
  }


lemma FORALLAWNMFUCKED(rv : Klon, other : Klon)
  requires forall x <- rv.m.Keys :: rv.AreWeNotMen(x,rv)
  ensures  forall x <- rv.m.Keys :: other.AreWeNotMen(x,rv)
  {
    reveal rv.AreWeNotMen();
    assert  forall x <- rv.m.Keys :: other.AreWeNotMen(x,rv);
  }




  function nu(k : Object, v : Object) : set<Object>
  {
    if (k==v) then {} else {v}
  }


function nu3(os : set<Object>, k : Object, v : Object) : (onu : set<Object>)
    ensures (k==v) ==> (onu == os)
    ensures (k!=v) ==> (onu == os+{v})
  {
    if (k==v) then (os) else (os+{v})
  }



  lemma funu(k : Object, v : Object)
    ensures nu(k,v) <= {v}
  {}

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
  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 20 //Klone_Via_Map

  requires m'.calid()
  requires a in m'.oHeap  //technically redundant given COKx
  requires COK(a, m'.oHeap) //ties owners into OHEAP but not KLON MAP

 //FROMHERE
  ensures  m.calid()

  ensures  a in m.m.Keys
  ensures  m.m[a] == b
  ensures  m.m[a] == b
  ensures  b in m.m.Values
//  ensures  COK(b,m.oHeap+m.ns)

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
  // should decided whether to do this with AMFOs or owners
  // and don one one...
  //OK os THIS requires us to make sure all the owners are in (even if outsidef - where does that happen?)
  ensures  m.from(m')
  //ensures b.AMFO == mapThruKlon(a.AMFO, m) //hmmm - bit it's NOT there

  // ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.ns)

  ensures klonOwnersAreCompatible(a, b, m)

  ensures b.fieldModes == a.fieldModes

//TOHERE

  //  ensures  fresh(b)
  //modifies m'[a]
  //  modifies m'.ns`fields //argh. pity so wide
  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  // modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  modifies {} // only modifes objecst allocated after this point?
{
  m := m';

  assert m.calid();
  assert MCALID: m.calid();

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

  //at some point - double check that the ubvaruabnts
  /// mean if a in m.m.Keys, a.AMFO in m.m.Keys too...
  /// not least because that pushes b into m.m.Values...
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
              assert klonVMapOK(m.m) && a.AMFB <= m.m.Keys;
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


          assert klonOwnersAreCompatible(a, b, m) by {
              reveal m.calid();
              assert m.calid();
              reveal m.calidOK();
              assert m.calidOK();
              reveal m.calidObjects();
              assert m.calidObjects();
              reveal m.calidMap();
              assert m.calidMap();

              assert klonAllOwnersAreCompatible(m);

              assert klonOwnersAreCompatible(a, b, m);



          }


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
      by {
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
        assert a !in m.m.Keys;
        assert a in m.oHeap;
        assert m.oHeap !! m.ns;
        assert a !in m.ns;
      }

      m.WeAreDevo();

    assert not(inside(a,m.o));
    assert a !in m.m.Keys;
    assert m.calid();
    assert forall k <- m.m.Keys :: m.AreWeNotMen(k,m);
    assert a  in m.oHeap;
    assert a !in m.ns;

      Klon.AintNoSunshine(a,m);



      print "Hey Baby let's CLONE Outside\n";

      b := a;

  assert b.fieldModes == a.fieldModes;

      print "Yay babhy hyou got that done\n";


  assert a !in m.m.Keys;
  assert a in m.oHeap;
  assert m.oHeap !! m.ns by {
    reveal m.calid();
    assert m.calid();
    reveal m.calidObjects();
    assert m.calidObjects();
    assert m.oHeap !! m.ns;
  }
  assert outside(a,m.o);


  {
    reveal m.calid();
    assert m.calid();
    reveal m.calidOK();
    assert m.calidOK();
    assert CallOK(m.oHeap);
    a.CallMyOwnersWillWitherAway(a, m.oHeap);
  }


  {
    reveal m.calid();
    assert m.calid();
    reveal m.calidObjects();
    assert m.calidObjects();
    assert m.m.Keys <= m.oHeap;
    OutsidersArentMapValues(a,m);
  }

  reveal m.calidMap();
  assert m.calidMap();
  assert klonVMapOK(m.m);
  assert (forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys);
  assert (forall x <- m.m.Keys :: x.allExternalOwners() <= m.m.Keys);

  assert a !in m.m.Values;

  print "about to Clone_All_Owners()...";

  ///////////////////////////////////////////////////////////////
  var mc := Clone_All_Owners(a, m);
  ///////////////////////////////////////////////////////////////

  assert mc.from(m);
  assert a.owner <= mc.m.Keys;
  assert a.allExternalOwners() <= mc.m.Keys;
  assert mc.calid();

  m := mc;

  assert a.allExternalOwners() <= m.m.Keys;

  print "done clone all owners\n";


// / /  / / / / / / / / / / / / / / / / / / / / / / / / / / / /
// EVIL - compiedin from above
// / /  / / / / / / / / / / / / / / / / / / / / / / / / / / / /


  //if already in hash table - return it and be done!
  //not sure why this takes sooo long compared to other

  //at some point - double check that the ubvaruabnts
  /// mean if a in m.m.Keys, a.AMFO in m.m.Keys too...
  /// not least because that pushes b into m.m.Values...
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




// / /  / / / / / / / / / / / / / / / / / / / / / / / / / / / /
// EEND - compiedin from above
// / /  / / / / / / / / / / / / / / / / / / / / / / / / / / / /

  assert a !in m.m.Keys;
  assert m.calid();


  assert a.allExternalOwners() <= m.m.Keys;

    {
    reveal m.calid();
    assert m.calid();
    reveal m.calidObjects();
    assert m.calidObjects();
    assert m.m.Keys <= m.oHeap;
    OutsidersArentMapValues(a,m);
  }

  print "about to putOutside...";

assert  //James wonders if this shojuldb'e be AFTER the utinside?  ut perhas that tdoesn't work
//  && canVMapKV(m.m, a, a)
  && (a in m.oHeap)  //KJX do I want this here?
  && (a.AMFO <= m.m.Keys+{a})
//  && (mapThruVMapKV(a.AMFO, m.m, a, a) == a.AMFO)
//  && (a.owner <= a.AMFO)
    && (a.owner <= m.m.Keys+{a})

  && (a.fieldModes == a.fieldModes)
by {
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



}

//already have this!
//OutsidersArentMapValues(a,m);

assert outside(a, m.o);


RVfromCallOK(m.oHeap, m.oHeap);
assert a in m.oHeap;
assert m.o in m.oHeap;
assert a.Ready() && a.Valid();
assert m.o.Ready() && m.o.Valid();

OwnersAreOutsideFuckers(a, m.o);

// assert NIGEL:
  // && forall oo <- a.owner :: outside(oo,m.o)
  // && forall oo <- a.AMFO  :: outside(oo,m.o)
  // && forall oo <- a.allExternalOwners() :: outside(oo,m.o)
  // && (mapThruVMap(a.owner, m.m) == a.owner)
  // && (mapThruVMapKV(a.owner, m.m, a, a) == a.owner)//KJXOWNERS
    // && (mapThruVMapKV(a.AMFO, m.m, a, a)  == a.AMFO)
//  && forall oo <- a.AMFO  :: m.m[oo] == oo
//   by {
//         reveal m.calid();
//         assert m.calid();
//         reveal m.calidOK();
//         assert m.calidOK();
//         reveal m.calidObjects();
//         assert m.calidObjects();
//         reveal m.calidMap();
//         assert m.calidMap();
//         reveal m.calidSheep();
//         assert m.calidSheep();
//
//         assert forall oo <- a.allExternalOwners()  :: oo in m.m.Keys;
//         assert forall oo <- a.allExternalOwners()  :: m.m[oo] == oo;
//         assert forall oo <- a.owner :: outside(oo,m.o);
//         assert forall oo <- a.owner :: m.m[oo] == oo;
//         assert (set oo <- a.owner :: m.m[oo]) == a.owner;
//         assert mapThruVMap(a.owner, m.m) == a.owner;
//
//         assert forall oo <- a.AMFO :: (oo == a) || outside(oo,m.o);
//         assert forall oo <- a.AMFO :: (oo == a) || m.m[oo] == oo;
//         assert (set x <- {a} :: x) == {a};
//
//         MapThruIdentity((a.AMFO - {a}), m.m);
//         assert (set x <- (a.AMFO - {a}) :: m.m[x]) ==  (a.AMFO - {a});
//
//         IdentityExtensionality(a.AMFO - {a}, m.m, a);
//         assert (a.AMFO - {a})+{a} == (a.AMFO);
//         MapThruIdentity(a.AMFO, VMapKV(m.m,a,a));
//         assert mapThruVMapKV(a.AMFO, m.m, a, a) == a.AMFO;
//
//         assert forall oo <- a.AMFO  :: outside(oo,m.o);
//         assert a.owner <= a.AMFO;
//         assert forall oo <- a.owner :: outside(oo,m.o);
//
//   assert forall oo <- a.owner :: outside(oo,m.o);
//   assert forall oo <- a.AMFO  :: outside(oo,m.o);
//   assert forall oo <- a.allExternalOwners() :: outside(oo,m.o);
//   assert (mapThruVMap(a.owner, m.m) == a.owner);
//   assert a !in a.owner;
//   IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner, m.m, a, a);
//   assert (mapThruVMapKV(a.owner, m.m, a, a) == a.owner);
//
//   assert (mapThruVMapKV(a.AMFO, m.m, a, a) == a.AMFO);
//
//   }



  // assert DEREK: (mapThruVMapKV(a.AMFO, m.m, a, a)  == a.AMFO)
  //   by { reveal NIGEL; }

assert klonCanKV(m, a, a) by {

assert (a == b);

  // reveal DEREK;
  //body of klonCanKN expanded inline
  assert canVMapKV(m.m, a, a);
  assert (a in m.oHeap);
  assert (if (a==a) then (a in m.oHeap) else (a !in m.oHeap));
  assert (a.owner <= m.m.Keys+{a});
//  assert (mapThruVMapKV(a.owner, m.m, a, a) == a.owner);
  assert (a.AMFO <= m.m.Keys+{a});
//  assert (mapThruVMapKV(a.AMFO, m.m, a, a) == a.AMFO);
  assert (a.fieldModes == a.fieldModes);


assert m.boundsNestingOK(a, m.oHeap);
m.widerBoundsNest(a, m.oHeap, m.oHeap+m.ns+{a});
assert m.boundsNestingOK(a, m.oHeap+m.ns+{a});

assert a.allExternalOwners() <= m.m.Keys ;
InTHeBox(a,m);
assert m.boundsNestingOK(a, m.m.Keys+{a});

  //this is cloneOUTSIDE -= so a == b?  riugbht??

  // && m.boundsNestingOK(b, m.oHeap+m.ns)
  // && m.boundsNestingOK(a, m.m.Keys+{a})
  // && m.fieldMappingsOK(a, b, m.m.Keys+{a});

}  ///end KlonKV

{
  reveal m.calidSheep();
  assert m.calidSheep();
  reveal m.AreWeNotMen();
  assert forall k <- m.m.Keys :: m.AreWeNotMen(k,m);
  assert m.AreWeNotMen(a, klonKV(m,a,a));

    ///////////////////////////////////////////////////////////////
  m := m.putOutside(a);   ///HOPEY?  CHANGEY?
    print "done? rashy?  washy?\n";
  ///////////////////////////////////////////////////////////////


}

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

  ///////////////////////////////////////////////////////////////
      b, m := Clone_Clone_Clone(a, m);
  ///////////////////////////////////////////////////////////////

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
  assert b in m.m.Values;
  COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
  assert COK(b, m.oHeap+m.ns);
  assert BOK: COK(b, m.oHeap+m.ns);
  //  assert fresh(b);   //umm, yeah should probalboy be fresh at least if INSIDE, but...
  //  have to experiment with a clause somewhere in calidSheep saying every inside clone is new
  //  or everyhing in ns2 is new. or...
  //   assert b in m.ns;

  assert m.m[a] == b;
  assert a !in m'.m.Keys;
  // assert b !in m'.oHeap;   //need to decided whet)her this is (nominally) both iunsier or outside, or just inside
  //assert b !in m'.ns;;


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

  assert COK(b, m.oHeap+m.ns) by { reveal BOK; }

  assert m.from(m');
  //  }
  print "RETN Clone_Via_Map:", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

}





method Clone_All_Fields(a : Object, b : Object, m' : Klon)
  returns (m : Klon)
  //clone all fields a.n into b.n
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
//  requires b.AMFO == mapThruKlon(a.AMFO, m')  //KJXFRIDAY13TH
//  requires b.AMFO <= m'.m.Values
  requires b.AMFO <= m'.oHeap+m'.ns

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

// assert b.AMFO == mapThruKlon(a.AMFO, m');
assert b in m'.m.Values;
assert m'.m[a] == b;  //mmmKJX

//TUESDAY15DEC2024

assert b.AMFO <= (m'.oHeap+m'.ns)
by
   {
      assert COK(b,m'.oHeap+m'.ns);
      reveal COK();
   }

// assert (b.AMFO <= m'.m.Values) by {
//   assert m'.calid() by { reveal MPRIME; }
//   reveal m'.calid(), m'.calidMap();
//   assert m'.calidMap();
//   assert (forall x <- m'.m.Keys ::
//         && m'.boundsNestingOK(m'.m[x], m'.oHeap+m'.ns));
//
//   assert a in m'.m.Keys;
//   assert b in m'.m.Values;
// `  assert COK(b,m'.oHeap+m'.ns);`
//   assert m'.boundsNestingOK(b, m'.oHeap+m'.ns);
//   assert ownerInsideOwnerInsideOwner(m'.oHeap+m'.ns, b.AMFO, b.AMFB);
// }

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

//////////////////////////////////////////////////////
//preconditions for Clone_Field_Map(a,n,b,m);
//////////////////////////////////////////////////////

  assert m.calid();
  assert COK(a, m.oHeap);
  assert COK(b, m.oHeap+m.ns);

  assert n  in a.fields.Keys;
  assert n !in b.fields.Keys;

  assert n  in a.fieldModes;
  assert n  in b.fieldModes;
  assert a.fieldModes == b.fieldModes;
  assert FLDMODZ: a.fieldModes == b.fieldModes;
  assert a in m.oHeap;
  assert a in m.m.Keys;
  assert a.AMFO <= m.m.Keys;
  assert b in m.ns;
  assert b in m.m.Values;
//  assert b.AMFO <= m.m.Values;
  assert b  in m.oHeap+m.ns; //TUESDAY17DEC2024
  assert (a in m.m.Keys) && m.m[a] == b;
  assert m.o    in m.oHeap;
  assert m.m.Keys   <= m.oHeap;
  assert forall n <- b.fields :: (n in b.fieldModes) && AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
  assert refOK(a, a.fields[n]);




  assert m.calid();
  assert COK(a, m.oHeap);
  assert COK(b, m.oHeap+m.ns);

  assert n  in a.fields.Keys;
  assert n !in b.fields.Keys;

  assert n  in a.fieldModes;
  assert n  in b.fieldModes;
  assert a.fieldModes == b.fieldModes;
  assert a.fieldModes == b.fieldModes;
  assert a in m.oHeap;
  assert a in m.m.Keys;
  assert a.AMFO <= m.m.Keys; //KJX should be part of some invariant;
  assert b in m.ns;
  assert b in m.m.Values;
  assert b.AMFO <= m.oHeap+m.ns  ;
  assert (a in m.m.Keys) && m.m[a] == b;
  assert m.o    in m.oHeap;
  assert m.m.Keys   <= m.oHeap;
  assert forall n <- b.fields :: (n in b.fieldModes) && AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
  assert refOK(a, a.fields[n]);




    rm := Clone_Field_Map(a,n,b,m);

//////////////////////////////////////////////////////

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
  //        //assume COK(b, m.oHeap + m.ns);
  //        //assume m'.m.Values - {b} + {b} == m'.m.Values;
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
//     COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);s
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
//   assert a.AMFO - {a}  <= rm.m.Keys;t
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


// method Clone_KaTHUMP(a : Object, m' : Klon)
//   //spike method to test AMFO being "owner-closed"
//   //means the clones are "owner-cooned"
//   // that all the owners (and their AMFOS) are in the current objects AMFOS
//   //  i.e,  forall oo <- MYOWNERS :: oo in oo.AMFO
//   //  forall oo <- MYOWNERS - this? :: oo.AMFO <= this.AMFO..
//   // so if .e.g a[x] == c,   then we want m[a[x]] == m[c]...
//   // (please James, write a comment about what yhis method is doing]
//   returns (b : Object, m : Klon)
//   decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_Heap
//
//   //this case
//   requires a !in m'.m.Keys
//   requires inside(a,m'.o)
//
//   //extraOK  requires a.extra == {} //extra not yet clone
//
//
//   //all Clone_
//   requires m'.calid()
//   requires a in m'.oHeap
//   requires COK(a, m'.oHeap)
//
//   //from clone extra owners
//   ensures  m.calid() //needed to be able to call some of the below  en
//   //ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...  //kathump
//   ensures  m.from(m')
//
//   // ensures  a !in m'.m.Keys ==> b !in m'.ns
//   // ensures  b  in m'.ns ==> a  in m'.m.Keys
//
// { //kathump
//
//   m := Clone_All_Owners(a, m');
//   b := a;  //OOPS!  //KJX WHAT THE FUICKY FUCK FUCK
//
//   assert m.calid();
//   reveal m.calid();
//   assert m.calidObjects();
//   reveal m.calidObjects();
//   assert m.calidOK();
//   reveal m.calidOK();
//   assert m.calidMap();
//   reveal m.calidMap();
//   assert m.calidSheep();
//   reveal m.calidSheep();
//   COKfromCallOK(a, m.oHeap);
//   assert COK(a, m.oHeap);
//   reveal COK();
//   assert a.Ready();
//   assert a.owner <= a.AMFO;
//   assert COK(m.o, m.oHeap);
//   assert CallOK(m.oHeap);
//   COKAMFO(a, m.oHeap);
//   assert CallOK(a.AMFO, m.oHeap);
//   assert a.owner <= a.AMFO;
//   CallOKNarrowFocus(a.owner, m.oHeap);
//   assert CallOK(a.owner, m.oHeap);
//
//   //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //
//
//   assert AllTheseOwnersAreFlatOK(a.AMFO - {a});
//   //  reveal AllTheseOwnersAreFlatOK();
//   assert OrigBigfoot(a.AMFO - {a});
//
//   assert flattenAMFOs(a.owner) == a.allExternalOwners();
//   assert OrigBigfoot(a.allExternalOwners());
//   assert AllTheseOwnersAreFlatOK(a.allExternalOwners()) by
//   {
//     reveal AllTheseOwnersAreFlatOK();
//     assert AllTheseOwnersAreFlatOK(a.allExternalOwners());
//   }
//   //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //
//
//
//   // assert a.allExternalOwners() <= m.m.Keys;
//
//   //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //
//
//
//   assert  m.from(m');
//
//
//   //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //
//
//   // assert  a !in m'.m.Keys ==> b !in m'.ns;
//   // assert  b  in m'.ns ==> a  in m'.m.Keys;
// }


//r2


method Clone_Clone_Clone(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //actually does the clone....
  // was the old Clone_Inside_Heap

    decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15

  //this case
  requires inside(a,m'.o)
  requires a !in m'.m.Keys

  //all Clone
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)
  //requires COK(a, m'.m.Keys+{a}) //KJXFUCKEDFRIDAY13TH

  ensures  m.calid()
  ensures  a in m.m.Keys
  ensures  b in m.m.Values
    ensures  a in m.m.Keys && m.at(a) == b
//  ensures  b in m.ns
//  ensures  COK(b, m.oHeap+m.ns)

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
//  ensures b.AMFO <= m.m.Values //do we want COK B here too? ///TUESDAY17DEC2024
  ensures b.AMFO <= m.oHeap+m.ns //TUESDAY17DEC2024
  ensures old(m'.calid())
  ensures m.from(m')

  ensures klonOwnersAreCompatible(a, b, m)

//
//   //ensures b.AMFO == set x <- a.AMFO :: m.m[x]
//
  ensures b.fieldModes == a.fieldModes
//   //   ensures b.fields.Keys == a.fields.Keys

  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  //modifies (set o : Object)`fields
  // ensures a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?   //Cline INsinside heap
  // ensures b in m'.ns ==> a in m'.m.Keys
  modifies {}
{ //clone inside heap
  m := m';


//b := a; return;///FUKOF  //16s!!!

  //FUKOF
  assert m.calid();
  assert inside(a,m.o);
  assert COK(a, m.oHeap);
//  assert COK(a, m.m.Keys+{a} );
//  assert AKKK: COK(a, m.m.Keys+{a} );


  print "Clone_Clone_CLone of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CIH ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

  assert CallOK(a.owner, m.oHeap) by {
    // assert COK(a, m.oHeap);
    m.calidOKFromCalid();
    // assert CallOK(m.oHeap);
    COKowner(a, m.oHeap);
    // assert CallOK(a.owner, m.oHeap);
  }

//     reveal m.calid();
//     assert m.calid();
//     reveal m.calidOK();
//     reveal m.calidOK();
//     assert CallOK(m.oHeap);
//
//     COKAMFO(a, m.oHeap);
//     assert CallOK(a.AMFO, m.oHeap);
//     assert (a.AMFO <= m.oHeap);
//
//     COKfromCallOK(a, m.oHeap);
//     assert COK(a, m.oHeap);
//     reveal COK();
//     assert a.Ready();
//     assert a.owner <= a.AMFO;
//     assert CallOK(a.owner, m.oHeap);
//
//
//     assert COK(m.o, m.oHeap);
//     assert CallOK(m.oHeap);
//     COKAMFO(a, m.oHeap);
//     assert CallOK(a.AMFO, m.oHeap);
//     assert a.owner <= a.AMFO;
//     CallOKNarrowFocus(a.owner, m.oHeap);
//     assert CallOK(a.owner, m.oHeap);
//
//   }

  //makde COK check for this, no need to do another level here?
  //... or do we - I don't (now) see why...
  // assert forall x <- a.extra :: COK(x,m.oHeap);
  // forall x <- a.extra ensures COK(x,m.oHeap)
  // {
  //   assert true;
  // }
  //assert CallOK(a.extra,m.oHeap);

assert AllTheseOwnersAreFlatOK(a.allExternalOwners()) by {
    //assert COK(a, m.oHeap);
    m.calidOKFromCalid();
    //assert CallOK(m.oHeap);
    COKowner(a, m.oHeap);
    //assert AllTheseOwnersAreFlatOK(a.allExternalOwners());
  }

//   assert (flattenAMFOs(a.owner) < a.AMFO) by {
//     assert m.calid();
//     reveal m.calid();
//     assert m.calidOK();
//     reveal m.calidOK();
//     COKfromCallOK(a, m.oHeap);
//     assert COK(a, m.oHeap);
//     reveal COK();
//     assert a.Ready();
//     assert a.AMFO > flattenAMFOs(a.owner);
//     assert flattenAMFOs(a.owner) <=  a.AMFO;
//   }
//
// assert AllTheseOwnersAreFlatOK(a.owner, a.AMFO)
//   by { reveal AllTheseOwnersAreFlatOK(); }
//

//b := a; return;///FUKOF  //16s

  print "Clone_Clone_CLone ", fmtobj(a), " calling if", fmtown(a.owner) ,"\n";

  //extraOK        reveal COK(); assert a.owner.extra == {}; //extra not yet cloned

assert ((m'.oHeap - m'.m.Keys),10 decreases to (m.oHeap - m.m.Keys),5);

  assert ((m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15
    decreases to
      (m.oHeap - m.m.Keys), a.AMFO, (a.fields.Keys), 12);



/////////////////////////////////////////////////////////////////////////////////
  var rm := Clone_All_Owners(a, m);
/////////////////////////////////////////////////////////////////////////////////

//note that BOUNDS are subtypes of OWNERS BOWIE  KJXBOUNDS

  assert rm.from(m);
  assert rm.calid();
  assert a.owner <= rm.m.Keys;
  assert AOLTK: a.owner <= rm.m.Keys;
  assert a.allExternalOwners() <= rm.m.Keys;
  assert mapThruKlon(a.allExternalOwners(),rm) <= rm.m.Values;

RVfromCOK(a, rm.oHeap);
AMFUCKED(a);
  assert a.AMFO == flattenAMFOs(a.owner) + {a} by { reveal COK(); }
  assert mapThruKlon(a.AMFO - {a}, rm) <= rm.m.Values;
  assert a in a.AMFO;
  assert flattenAMFOs(a.owner) == a.AMFO - {a};

  assert rm.m.Values >= m.m.Values;

  assert rm.oHeap == m.oHeap;
  rm.boundsNestingFromCalid(a,rm.oHeap);

assert a.allExternalOwners() >= a.allExternalBounds();

  rm.calidOKFromCalid();
  assert COK(a, rm.oHeap);
     {  assert AOK: COK(a, rm.oHeap); }
//assert COK(a, rm.m.Keys+{a} ) by { reveal COK(), AKKK; }
//assert AKK: COK(a, rm.m.Keys+{a} );
  assert CallOK(rm.oHeap);
  COKowner(a, rm.oHeap);
  assert a.AMFO == flattenAMFOs(a.owner) + {a} by { reveal COK(); }
  //assert flattenAMFOs(a.owner) == a.allExternalOwners();
  assert a.AMFO == a.allExternalOwners() + {a} by { reveal COK(); }
  assert a.allExternalOwners() == a.AMFO - {a} by
     { reveal COK(); assert COK(a, rm.oHeap); assert a.Ready(); assert a.OwnersValid();
       assert (a.AMFO == (a.allExternalOwners() + {a})) by { reveal COK(); }
       LemmaSetXsPlusSeperateSingleton(a.allExternalOwners(), a, a.AMFO);
       assert a.allExternalOwners() == a.AMFO - {a};
          }
  assert a !in a.owner;
  //assert a !in flattenAMFOs(a.owner);
  assert a.Ready() by { assert rm.calid(); rm.calidOKFromCalid(); assert COK(a, rm.oHeap); reveal COK(); }
  assert a.allExternalOwners() == flattenAMFOs(a.owner);

//  assert mapThruKlon(a.allExternalOwners() , rm) == mapThruKlon(flattenAMFOs(a.owner), rm);

//KJXFRI20DEC2024
  // var rowner := mapThruKlon(a.owner, rm); //needs to go!
  // var rbound := mapThruKlon(a.bound, rm); //DITTO...

assert COK(a, rm.oHeap);

 var rowner := a.owner;
 var rbound := a.bound;
//KJXFRI20DEC2024
assert CallOK(rowner, rm.oHeap);
CallOKWiderContext(rowner, rm.oHeap, rm.ns);
CallOKNarrowFocus(rbound, rowner, rm.oHeap+rm.ns);


// var BAXO := mapThruKlon(a.allExternalOwners(),rm);
//
// assert BAXOK: BAXO == mapThruKlon(flattenAMFOs(a.owner), rm) <= rm.m.Values;


//assert BAXO == flattenAMFOs(mapThruKlon(a.owner, rm));

  // var rAMXO  := mapThruKlon(a.allExternalOwners(),  rm); //why this, why not a.AMFO?  --- cos b hasn't been created yet!
  // var rAMXB  := mapThruKlon(a.allExternalBounds(),  rm);   //grr...



  var rAMXO := flattenAMFOs(rowner);
  var rAMXB := flattenAMFOs(rbound);

assert rAMXO >= rAMXB;
assert ownerInsideOwner(rAMXO,rAMXB);

  // assert ROWNER_RM: rowner == mapThruKlon(a.owner, rm);

  assert rm.calid();
  assert a.owner <= rm.m.Keys;
  assert a.allExternalOwners() <= rm.m.Keys;
  assert a.allExternalOwners() == flattenAMFOs(a.owner);


  OwnersValidFromCalid(a,rm);

  assert a.bound <= rm.m.Keys;
  assert a.allExternalBounds() <= rm.m.Keys;

  assert a.allExternalBounds() == flattenAMFOs(a.bound);
  assert AllTheseOwnersAreFlatOK(a.allExternalBounds()) by
    { reveal AllTheseOwnersAreFlatOK();
      assert AllTheseOwnersAreFlatOK(a.allExternalBounds()); }
//  mapThruKlonPreservesFlatness3(a.owner, a.allExternalOwners(), rowner, rAMXO, rm);
//  mapThruKlonPreservesFlatness3(a.bound, a.allExternalBounds(), rbound, rAMXB, rm);

//b := a; return;///FUKOF  //20s


  print "Clone_Clone_CLone ", fmtobj(a), " Clone_All_Owners RETURNS ", fmtown(rowner) ,"\n";



    //better name woiuld be: all All_Owners_Are_Keys or sometghung
//AMFOsFromOwnersFromCalid(a, rm);
    // except we //assume this is true or the above call wouldn't work...?



//  mapThruKlonPreservesAMFO(a.owner, rowner, rm);
 assert CallOK(rowner, rm.oHeap+rm.ns);
//  mapThruKlonPreservesAMFO(a.bound, rbound, rm);
 assert CallOK(rbound, rm.oHeap+rm.ns);

//  mapThruKlonPreservesAMFO(a.allExternalOwners(), rAMXO, rm);
//  mapThruKlonPreservesAMFO(a.allExternalBounds(), rAMXB, rm);


assert AllTheseOwnersAreFlatOK(a.allExternalOwners());
/// mapThruKlonPreservesFlatness2(a.allExternalOwners(), rAMXO, rm);
FlatAMFOsAreFlat(rowner,rAMXO,rAMXO);
assert AllTheseOwnersAreFlatOK(rowner,rAMXO);


//KJX - I find this unimpressive
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

    rm.calidOKFromCalid();

//   assert CallOK(a.owner, rm.oHeap);
//   assert CallOK(rm.oHeap);
//   assert CallOK(rm.m.Keys, rm.oHeap);
//   assert CallOK(rm.m.Values, rm.oHeap+rm.ns);
//   assert CallOK(rm.ns, rm.oHeap+rm.ns);

//KJX what the shit is going on here.
//where am I going now?
//
//   //should we rename oHeap as context?
//   //KJX why do we care about this?
//   assert COK(rm.o, rm.oHeap);
//   assert CallOK(rm.oHeap);
//
//
//   // COKAMFO(rowner, rm.oHeap+rm.ns);
//   // assert {rowner}+rowner.AMFO == rowner.AMFO+{rowner};
//   // assert CallOK({rowner}+rowner.AMFO,
//   //
//   // assert CallOK({rowner}+rowner.AMFO, rm.oHeap+rm.ns);
//
//
//   assert CallOK(rm.oHeap); //ensured by clone
//   CallOKWiderContext(rm.oHeap,rm.oHeap,rm.ns);
//   assert CallOK(rm.oHeap,rm.oHeap+rm.ns);
//
//   assert CallOK(rm.ns, rm.oHeap+rm.ns);  //ensured by clone
//   CallOKWiderFocus(rm.oHeap, rm.ns, rm.oHeap+rm.ns);
//
//   assert CallOK(rm.oHeap+rm.ns);
//
//   assert CallOK(rowner, rm.oHeap+rm.ns);  //ensured by clone
//
// ///need this for later...
//   // assert OKR0: CallOK(rowner, rm.oHeap+rm.ns);
//   // assert OKC0: CallOK(rm.oHeap+rm.ns);
// ///...or rather turns out we DONT


  if (a in rm.m.Keys) {

    print "Clone_Clone_CLone ", fmtobj(a), " already cloned: abandoning ship!!\n";


    m := rm;
//    b := m.at(a);
    b := m.at(a);

    assert b in rm.m.Values;
    assert CallOK(rm.m.Values, rm.oHeap+rm.ns);
    assert CallOK(rm.ns, rm.oHeap+rm.ns);
COKfromCallOK(b, rm.m.Values,rm.oHeap+rm.ns);

//
//     assert b.owner == rowner;
//     assert b.AMFO  == mapThruKlon(flattenAMFOs(a.owner), rm) + {b};

//FUCKOFF commente out becauyse FUCKOFF
//     assert m.calid();
//     assert CallOK(m.m.Values, m.oHeap+m.ns);
//     assert b in m.m.Values;
//     assert m.m.Values == m.m.Values;
//     assert b in m.m.Values;
//     assert (b in m.ns) by
//     {
//       reveal m.calid();
//       assert m.calid() && m.calidObjects() && m.calidOK() && m.calidSheep();
//       reveal m.calidSheep();
//       reveal m.AreWeNotMen();
//       assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
//       assert b == m.m[a];
//       assert a in m.m.Keys;
//       assert inside(a,m.o);
//       assert m.m[a] in m.ns;
//       assert b in m.ns;
//     }
//     assert b in m.ns;
//     assert b in rm.ns;
//
//     COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
//     assert COK(b, m.oHeap+m.ns+{b});
//     assert COK(b, rm.oHeap+rm.ns+{b});
//
//     assert b.fieldModes == a.fieldModes;
//     assert m.calidSheep();
//
//     assert m.m.Keys >= m'.m.Keys + {a};


// assert BAXO == mapThruKlon(flattenAMFOs(a.owner), rm) <= rm.m.Values
//  by { reveal BAXOK; }

//but of course we don't know that BNAXO is actuall rm.m.AMFO
///although it is! --- for now

assert rm.calid();
//assert COK(b, m.m.Values);  //KJXTUESDAY17DEC

assert COK(b, rm.oHeap+rm.ns);

TargetOwnersReallyAreOK(b, rm);

//     assert b in m.m.Values;
//     assert b.AMFO == BAXO + {b};
//     assert b.AMFO <= m.m.Values;
//
//     assert m.m.Values >= m'.m.Values + {b};


//END FUCKOFF

    return;
  } // a in rm.m.Keys - i.e. randomly done while cloning owners



//b := a; return;///FUKOF  //19s with just return if a cloned h7 clone_owner
//b := a; return;///FUKOF  //20s+ with full code if a cloned h7 clone_owner

  print "Clone_Clone_CLone ", fmtobj(a), " have rowner ", fmtown(rowner) ," self not yet cloned\n";
//
//   assert a !in rm.m.Keys;
//   assert a.owner <= rm.m.Keys;
//
//   assert CallOK(rowner, rm.oHeap+rm.ns);
//   assert CallOK(rm.oHeap+rm.ns);
//   CallOKNarrowFocus({},rm.oHeap+rm.ns);    //WTF is this doiung?  why?
//   assert CallOK({},rm.oHeap+rm.ns);        //and this one?
//
//
// ///need this for later...
//   assert OKR1: CallOK(rowner, rm.oHeap+rm.ns);
//   assert OKC1: CallOK(rm.oHeap+rm.ns);

//
//   var rrm := Clone_All_Owners(a, rm);
//   assert rrm.from(rm);
//
//   assert CallOK(rrm.oHeap);
//   assert CallOK(rrm.oHeap, rrm.oHeap);
//   assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);
//   CallOKWiderContext(rrm.oHeap, rrm.oHeap, rrm.ns);
//   CallOKWiderFocus(rrm.oHeap, rrm.ns, rrm.oHeap+rrm.ns);
//   assert OKC2: CallOK(rrm.oHeap+rrm.ns);
//
// ///need this for later...
//
//   //COKWiderContext2(rowner, )
//
//   CallOKWiderContext2(rowner, rm.oHeap+rm.ns, rrm.oHeap+rrm.ns);
//   assert OKR2: CallOK(rowner, rrm.oHeap+rrm.ns);
//
//
//   assert a.owner <= rm.m.Keys;
//   assert a.owner <= rrm.m.Keys;
//
//   if (a in rrm.m.Keys) {
//
//     print "Clone_Clone_Clone ", fmtobj(a), "after Clone_Extra_Oners, seems a already cloned: abandoning ship!!\n";
//
//     m := rrm;
//
//     b := rrm.at(a);
//
//     assert rrm.calid();
//
//     reveal rrm.calid();
//     reveal rrm.calidObjects();
//     reveal rrm.calidOK();
//     reveal rrm.calidMap();
//     reveal rrm.calidSheep();
//     reveal rrm.AreWeNotMen();
//
//     assert rrm.calid();
//     assert rrm.calidObjects();
//     assert rrm.calidOK();
//     assert rrm.calidMap();
//     assert rrm.calidSheep();
//
//     assert inside(a, rrm.o);
//     assert (forall x <- rrm.m.Keys :: rrm.AreWeNotMen(x, rrm));
//     assert rrm.AreWeNotMen(a,rrm);
//     assert (inside(a,rrm.o)) ==> rrm.m[a] in rrm.ns;
//     assert b == rrm.m[a];
//
//     assert b in rrm.ns;
//     assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);
//     COKfromCallOK(b, rrm.ns, rrm.oHeap+rrm.ns);
//     assert COK(b, rrm.oHeap+rrm.ns);
//
//     return;
//   }

var rrm := rm; //KJX THIS IS EVIL, should clean up and get rid of rrm completel6.
assert rrm.from(rm);

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
//assert COK(a, rrm.m.Keys+{a} ) by { reveal AKK; }

  reveal COK();
  assert a.allExternalOwners() <= rrm.oHeap;
  assert a !in rrm.m.Keys; // by { reveal ANKS; }



//FROM HERE
//
//   assert OKR3: CallOK(rowner, rrm.oHeap+rrm.ns);
//   assert OKC3: CallOK(rrm.oHeap+rrm.ns);
//
  //preconditions for cake...
  // assert CallOK(rowner, rrm.oHeap+rrm.ns) by { reveal OKR3, OKC3; }
  // assert CallOK(rrm.oHeap+rrm.ns) by { reveal OKR3, OKC3; }
//
//
//   assert (a.AMFO - {a}) == a.allExternalOwners();
//   assert flattenAMFOs(a.AMFO - {a}) == flattenAMFOs(a.allExternalOwners());
//
//   assert a.allExternalOwners() + {a} == a.AMFO;
//   // assert flattenAMFOs(a.owner) + a.extra == (a.AMFO - {a}) == a.allExternalOwners();
//   //
//   // reveal AllTheseOwnersAreFlatOK();
//   //
//   //        assert AllTheseOwnersAreFlatOK(a.AMFO - {a}) by { reveal aFLAT; }
//   //        assert AllTheseOwnersAreFlatOK(flattenAMFOs(a.owner) + a.extra);
//   var aAMFOs := a.allExternalOwners() + {a};
//   //  assert AllTheseOwnersAreFlatOK(aAMFOs);https://www.youtube.com/
//
//
//
//   //assert forall ax <- a.extra :: imageUnderMap(ax, rrm.m[ax], rrm);
//   assert rowner == mapThruKlon(a.owner, rrm);
//   assert a.allExternalOwners() <= rrm.m.Keys;
//   //assert forall ao <- flattenAMFOs(a.owner) :: rrm.m[ao] in (rrm.m[a.owner]).AMFO;
//
//
//
//
//   // assert OrigBigfoot(flattenAMFOs(a.owner));
//   // assert AllTheseOwnersAreFlatOK(flattenAMFOs(a.owner));
//
//
//
//   //reveal AllTheseOwnersAreFlatOK();
//
//   //assert rowner.AMFO ==  mapThruKlon(flattenAMFOs(a.owner), rrm);
//   //        assert AllTheseOwnersAreFlatOK(flattenAMFOs(a.owner) + a.extra);
//   //
//   //        assert AllTheseOwnersAreFlatOK(rowner.AMFO);
//   //
//   //        assert AllTheseOwnersAreFlatOK(a.extra, a.allExternalOwners());
//
//
//   //
//   //       assert (set o <- a.extra ::  rrm.m[o]) == mapThruKlon(a.extra, rrm);
//   //       assert (set o <- a.extra, oo <- o.AMFO ::  rrm.m[oo])
//   //          == mapThruKlon((set o <- a.extra, oo <- o.AMFO :: oo), rrm);
//   //
//   // assert mapThruKlon(aAMFOs, rrm) == amfosToBeMinusThis;
//
//   //  assert ((set o <- a.extra, oo <- o.AMFO :: oo) + a.extra)   //tnis should not worj!!!
//   //           ==  flattenAMFOs(mapThruKlon(a.extra,rrm));
//
//   reveal AllTheseOwnersAreFlatOK();
//   assert AllTheseOwnersAreFlatOK(rowner); ///this one is OK...
//
//
//
//   var R := rrm.m; //KJX and YEET AGAIN.  WTFFF. clean up!!
//   assert AllMapEntriesAreUnique(R);
//
//   assert klonVMapOK(R);
//
//   assert  (forall x <- R.Keys, oo <- x.AMFO  :: R[oo] in R[x].AMFO);
//
//   assert flattenAMFOs(a.owner) <= R.Keys;
//
//   //
//   //   //these dont work either
//   //   assert (forall o <- a.extra, oo <- R[o].AMFO ::
//   //             && ((oo in rowner.AMFO) || (oo in rextra)))
//   //     ;
//
//   //        assert (forall o <- rextra, oo <- o.AMFO ::
//   //             &&
//   //       ;
//   //
//
//   //assert flatAMFOs == ((set o <- a.extra, oo <- o.AMFO :: oo) + a.extra);
//
// ////KJX  assert rowner.AMFO <= amfosToBeMinusThis;
//
//   reveal AllTheseOwnersAreFlatOK();
//
//   //       var R := rrm.m;
//   //       assert AllMapEntriesAreUnique(R);
//   //       var M := invert(R);
//   //       assert AllMapEntriesAreUnique(M);
//   //
//   //       assert forall r <- R.Keys :: M[R[r]] == r;
//
//
//   //assert (forall o <- rextra :: o.AMFO <=  (rowner.AMFO+rextra));
//   // assert (forall o <- rextra, oo <- o.AMFO :: ((oo in rowner.AMFO) || (oo in rextra)));
//   // assert (forall o <- rextra :: o.AMFO <=  (rowner.AMFO+rextra));
//
//
//   assert Bigfoot(rowner);  //both originally had a .AMFO on the end - do we need it?  yes?  no?  what's the difference?
//   assert AllTheseOwnersAreFlatOK(rowner);
//   assert AllTheseOwnersAreFlatOK(rAMXO);
//
//
//   // assert Bigfoot((rextra), (rowner.AMFO+rextra));
//   // assert AllTheseOwnersAreFlatOK((rextra), (rowner.AMFO+rextra));
//
  var context := rrm.oHeap+rrm.ns;    ///why haul ns in here??? --- cos this the owners for the clone!  - the clowners!
  assert CallOK(rowner, context);

  rrm.calidOKFromCalid();
  assert CallOK(rrm.oHeap);
  CallOKWiderContext(rrm.oHeap, rrm.oHeap, rrm.ns);
  assert CallOK(rrm.oHeap,rrm.oHeap+rrm.ns);

  rrm.calidOKFromCalid();
  assert CallOK(rrm.ns, rrm.oHeap+rrm.ns);

  CallOKWiderFocus(rrm.oHeap, rrm.ns, rrm.oHeap+rrm.ns);
  assert CallOK(rrm.oHeap+rrm.ns, rrm.oHeap+rrm.ns);
  assert CallOK(rrm.oHeap+rrm.ns);
  assert CallOK(context);

FlatAMFOsAreFlat(rowner, rAMXO, rAMXO);
  assert AllTheseOwnersAreFlatOK(rowner, rAMXO);
  assert rAMXO >= flattenAMFOs(rowner);
  //     reveal AllTheseOwnersAreFlatOK();
  // assert AllTheseOwnersAreFlatOK(rowner);//both originally had a .AMFO on the end - do we need it?  yes?  no?  what's the difference?

//TO HERE


    assert forall o <- rowner :: o.Ready() by { reveal CallOK(), COK(); assert CallOK(rowner,context); }
    assert CallOK(rowner, rrm.oHeap+rrm.ns);
    assert CAOKRO: CallOK(rowner, rrm.oHeap+rrm.ns);
    assert CallOK(rrm.oHeap+rrm.ns); //KJX is this redundant Or wouidl it be redundat the other way around???
    // requires AllTheseOwnersAreFlatOK(oo)  //hmm? what would this mean?
    //requires CallOK({oo}+oo.AMFO, context)

    //KJX shouldn't there be some topological restriction on where or when
    //you can create new objects/contexts / regions?
    //what sgoiuld they be?

//  mapThruKlonPreservesAMFO(a.allExternalOwners(), rAMXO, rm);
//  mapThruKlonPreservesAMFO(a.allExternalBounds(), rAMXB, rm);

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
print "CALLING MAKE...";
  assert CallOK(rowner, rrm.oHeap+rrm.ns) by { reveal CAOKRO; }



  b := new Object.make(a.fieldModes, rowner, rrm.oHeap+rrm.ns, "clone of " + a.nick, rbound);
print "BACK FROM MAKE with ",fmtobj(b),"\n";
  assert b.fields == map[];

print "WTF\n";
//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

//  mapThruKlonPreservesAMFO(a.allExternalOwners(), rAMXO, rrm);
//  mapThruKlonPreservesAMFO(a.allExternalBounds(), rAMXB, rrm);

  assert fresh(b);
  assert b !in rrm.m.Values;
  assert b !in rrm.ns;
  assert b !in rrm.oHeap;
  assert b.fieldModes == a.fieldModes;
  assert b.owner == rowner;
  assert b.bound == rbound;
  // assert b.owner == mapThruKlon(a.owner, rrm) by { reveal ROWNER_RM; }

  assert b.owner == rowner;

  assert b !in rrm.oHeap;
  assert b !in rrm.m.Values;
  assert a !in rrm.m.Keys;
  assert COK(b, (rrm.oHeap+rrm.ns)+{b});
  // COKWiderContext(b, )
  // assert COK(b, {b} + rrm.oHeap+rrm.m.Values);


  assert b !in rrm.m.Values;
  assert COK(b, rrm.oHeap+rrm.ns+{b});
  assert B_NOTIN: b !in b.owner by {
    reveal COK();
    assert COK(b, rrm.oHeap+rrm.ns+{b});
    assert b.Ready();
    assert b.OwnersValid();
    assert b !in b.owner;
    }
  assert b !in (rrm.oHeap+rrm.ns);

  assert klonVMapOK(rrm.m);
  //assert forall kx <- a.extra :: rrm.m[kx] in b.extra;   //extra not yet cloned


  //extraOK        assert a.extra == {}; //extra not yet cloned
  assert a.allExternalOwners() <= rrm.m.Keys;
  assert a.allExternalBounds() <= rrm.m.Keys;

///PRECOND for putInsife
    assert rrm.calid();
    assert klonVMapOK(rrm.m); //lemma can derive from calid();

    assert canVMapKV(rrm.m,a,b);

        rrm.boundsNestingFromCalid(a,rrm.oHeap);
        assert (a.owner <= a.AMFO);
        assert (a.bound <= a.AMFB);
        assert (a.owner <= rrm.m.Keys+{a});
        assert (a.bound <= rrm.m.Keys+{a});
        assert canVMapKV(rrm.m, a, b);

        assert (a in rrm.oHeap);
        assert (a.AMFO <= rrm.m.Keys+{a});
        assert (a.AMFB <= rrm.m.Keys+{a});
        // assert (mapThruVMapKV(a.AMFO, rrm.m, a, b) == b.AMFO);

        assert rrm.calid();
        assert COK(b, (rrm.oHeap+rrm.ns)+{b});
        reveal COK();
        rrm.boundsNestingFromCalid(b,rrm.oHeap+rrm.ns+{b});

        //    assert (set i <- a.AMFB :: (rrm.m[a:=b])[i]) == b.AMFB;

//         assert (mapThruVMapKV(a.AMFB, rrm.m, a, b) == b.AMFB) by {
//
//
//
// //              assert klonKV(rrm,a,b).fieldMappingsOK(a, b, rrm.m.Keys+{a});
//
//               mapThruKlonPreservesAMFO(a.allExternalOwners(), rAMXO, rm);
//               mapThruKlonPreservesAMFO(a.allExternalBounds(), rAMXB, rm);
//
//               assert a.AMFO == a.allExternalOwners() + {a};
//               assert a.AMFB == a.allExternalBounds() + {a};
//
//               assert b.AMFO == rAMXO + {b};
//               assert b.AMFB == rAMXB + {b};
//         }

//GRR NEEDS to be the KV version               mapThruKlonIsMapThruVMap(a.AMFB, rrm, b.AMFB);
                //  assert b.AMFB == mapThruVMap(a.AMFB, rrm.m);
                //  IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.AMFB,rrm.m,a,b);
                //  assert b.AMFB == mapThruVMapKV(a.AMFB,rrm.m,a,b);
//
//         assert (mapThruVMapKV(a.AMFB, rrm.m, a, b) == b.AMFB) by{
//               assert b.owner == mapThruKlon(a.owner, rrm) by { reveal ROWNER_RM; }
//               assert a !in a.owner;
//               assert b !in b.owner;
//
//     assert rrm.calid();
//     assert a.owner <= rrm.m.Keys;
//     assert a !in rrm.m.Keys;
//     assert a !in a.owner;
//     assert b !in rrm.m.Values;
//     assert canVMapKV(rrm.m, a, b);
//
// IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner,rrm.m,a,b);
// //NoKeyNoProblems(a.owner,rrm,a,b);
// assert mapThruVMap(a.owner, rm.m) == mapThruVMapKV(a.owner, rrm.m, a, b);
//         }


        assert a.OwnersValid() by {
                assert unchanged(a);
                assert COK(a, m.oHeap) by { reveal AOK; }
                reveal COK();
                assert a.Ready();
                assert a.OwnersValid();
              }

// //assume false;
// b := a; return;///FUKOF  //15s

              IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner, rm.m, a, b);
              assert a !in a.owner;
//assert mapThruVMapKV(a.owner, rrm.m, a, b) == mapThruVMap(a.owner, rm.m);
              assert b.owner == rowner;
//              assert b.owner  == mapThruKlon(a.owner, rm);
           assert a !in a.owner && b !in a.owner;
//              assert b.owner  == mapThruKlon(a.owner, rrm);


//          asoiosert    b.owner  == mapThruVMap(a.owner, rrm.m)  == mapThruVMapKV(a.owner, rrm.m, a, b);

          assert BROWNER: b.owner  == rowner;
          assert a !in a.owner && b !in b.owner;
          IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner, rrm.m, a, b);
//Wed18Dec2024
//           NoKeyNoProblems(a.owner, rrm, a, b) by {
//               assert rrm.calid();
//               assert a.owner <= rrm.m.Keys;
//               assert a.bound <= rrm.m.Keys;
//               assert a !in rrm.m.Keys;
//               assert a !in a.owner;
//               assert a !in a.bound;
//               assert b !in rrm.m.Values;
//
// //not in there ytet,..              assert b in rrm.oHeap+rrm.ns;
//
//               assert klonCanKV(rrm, a, b) by {
//
//                   assert klonVMapOK(rrm.m);
//                   assert canVMapKV(rrm.m,a, b);
//                   assert a in rrm.oHeap;
//                   assert a != b;
//                   assert b !in rrm.oHeap;
//
//                   assert rrm.boundsNestingOK(a, rrm.oHeap);
//                   assert rrm.boundsNestingOK(b, rrm.oHeap+rrm.ns+{b});
//                   assert rrm.boundsNestingOK(a, rrm.oHeap+{a});
//
//                   // assert rrm.fieldMappingsOK(a, b, rrm.m.Keys);
//
//                   assert a.fieldModes == b.fieldModes;
//
//                   assert COK(a, m.oHeap) by { reveal AOK; }
// // assert COK(a, rrm.m.Keys+{a} ) by { reveal AKK; }
//                   rrm.boundsNestingFromCalid(a, rrm.oHeap);
//                   //assume a.bound <= a.owner;
//                   assert ownerInsideOwner(a.owner, a.bound);
//                   //assume a.AMFB <= a.AMFO;
//                   assert ownerInsideOwner(a.AMFO, a.AMFB);
//                   //assume a.bound <= a.AMFB;
//                   assert ownerInsideOwner(a.AMFB, a.bound);
//                   //assume a.owner <= a.AMFO;
//                   assert ownerInsideOwner(a.AMFO, a.bound);
//                   //assume a.bound <= a.owner <= rrm.m.Keys;
//                   assert ownerInsideOwnerInsideOwner(rrm.m.Keys, a.owner, a.bound);
//                   //assume a.AMFB <= a.AMFO   <= rrm.m.Keys;
//                   assert ownerInsideOwnerInsideOwner(m.oHeap, a.AMFO, a.AMFB);
//                   assert (a.AMFO-{a}) <= rrm.m.Keys;
//                   assert (a.AMFB-{a}) <= rrm.m.Keys;
//                   assert ownerInsideOwnerInsideOwner(rrm.m.Keys, a.AMFO-{a}, a.AMFB-{a});
//
//                   assert (a.AMFO) <= rrm.m.Keys+{a};
//
// assert COK(a, m.oHeap) by { reveal AOK; }
// assert COK(a, rrm.oHeap) by { reveal AOK; }
//
// COKNarrowContext(a, rrm.m.Keys+{a}, rrm.oHeap);
// assert COK(a, rrm.m.Keys+{a} );
//
//                   assert klonCanKV(rrm, a, b);
//               }
//
//               NoKeyNoProblems(a.owner, rrm, a, b);
//
//           }
//Wed18Dec2024
              assert rrm.calid();
              assert a.owner <= rrm.m.Keys + {a};
//              assert klonSatanKV(rrm, a, b);jjhhjj
//              assert mapThruKlon(a.owner, rrm)  == mapThruKlonKV(a.owner, rrm, a, b);
          // }

              NoKeyNoProblems(a.owner, rrm, a, b);
              assert rrm.calid();
              assert a.owner <= rrm.m.Keys + {a};
//              assert klonSatanKV(rrm, a, b);

          assert (b.AMFO >= b.AMFB >= a.AMFB);
              assert klonCanKV(rrm, a, b);

//          assert mapThruKlon(a.owner, rrm)  == mapThruKlonKV(a.owner, rrm, a, b);


// assert (mapThruVMapKV(a.owner, rrm.m, a, b) == b.owner);


        assert (a.fieldModes == b.fieldModes);


    assert klonCanKV(rrm,a,b);

    var km := klonKV(rrm,a,b); //there it go4s in!

    assert rrm.calid();
   klonCalidKVCalid(rrm,a,b,km);
//
assert km.calid(); //EVIL  (???? why is this evil?)
//
//     assert km.calid();

// //assume false;
//b := a; return;///FUKOF  //22s

//
//     assert km.calid() by {
//         reveal km.calid(), km.calidObjects(), km.calidOK(), km.calidMap(), km.calidSheep();
//
//         assert rrm.ns !! rrm.oHeap;
//         assert b !in rrm.oHeap;
//         assert km.ns == (rrm.ns + {b});
//         assert (rrm.ns + {b}) !! rrm.oHeap;
//
//         assert
//             && (km.o in km.oHeap)
//             && (km.m.Keys <= km.oHeap)
//             && (km.ns !! km.oHeap)
//             && (km.m.Values <= km.ns + km.oHeap)
//             && (km.ns <= km.m.Values)
//             ;
//
//         assert
//             && COK(km.o, km.oHeap)
//             && CallOK(km.oHeap)
//             && CallOK(km.m.Keys, km.oHeap) //HMMMM
//             && CallOK(km.m.Values, km.oHeap+km.ns)//HMMMM
//             && CallOK(km.ns, km.oHeap+km.ns) //HMMMM
//             ;
//
//         assert km.calidObjects();
//         assert km.calidOK();
//         assert km.calidMap();
//         assert km.calidSheep();
//         assert km.from(rrm);
//         assert km.calid();
//     }


 // //assume false;
//b := a; return;///FUKOF  //22s verifies!!

 assert a != b;
 assert km.ns == nu3(rrm.ns,a,b);
 assert km.ns == rrm.ns+nu(a,b);

//not quite shte why we need either of these
 AddToEmptySet(b);
 assert {b} == nu3({},a,b);
 assert nu(a,b) == {b};

//  // //assume false;
// b := a; return;///FUKOF  //WORKS 45s


    assert km.AreWeNotMen(a, km)  by {
      reveal km.AreWeNotMen();

      assert inside(a,rrm.o);
      assert forall k <- rrm.m.Keys :: rrm.AreWeNotMen(k,rrm);
      assert a !in rrm.m.Keys;
      assert b !in rrm.m.Values;

      assert inside(a,km.o);
      KlonKVExtendsTo(rrm, a, b, km);
      assert forall k <- rrm.m.Keys :: km.m[k] == rrm.m[k];
      assert forall k <- rrm.m.Keys :: rrm.AreWeNotMen(k,rrm);
FORALLAWNMFUCKED(rrm,km);
//      assert forall k <- rrm.m.Keys :: rrm.AreWeNotMen(k,km);

      assert inside(a,km.o);

      assert a in km.m.Keys;
      assert km.m[a] == b;

      assert UniqueMapEntry(km.m,a,b);
      assert UniqueMapEntry(km.m,a);

      assert b in km.ns;
      assert b == km.m[a];
      assert km.m[a] in km.ns;

    assert inside(a,km.o) ==> km.m[a] in km.ns;
    assert inside(a,km.o) ==> UniqueMapEntry(km.m,a);

      assert km.AreWeNotMen(a, km);
    }

//  // //assume false;
//  b := a; return;///FUKOF  //WORKS 45s

    assert km.AreWeNotMen(a, klonKV(rrm,a,b)) == km.AreWeNotMen(a, km);
    assert km.AreWeNotMen(a, klonKV(rrm,a,b));

assert km.AreWeNotMen(a, km);

    assert a  in rrm.oHeap;
    assert a !in rrm.m.Keys;
    assert b !in rrm.oHeap;
    assert b !in rrm.ns;
    assert b !in rrm.m.Values;
    assert COK(a, rrm.oHeap);
    assert COK(b, rrm.oHeap+rrm.ns+{b});
    assert rrm.m.Keys <= rrm.oHeap;
    assert a.allExternalOwners() <= rrm.m.Keys;
    assert b.allExternalOwners() <= rrm.oHeap+rrm.ns; //need to hae proceessed all owners first;

    assert (a.owner <= rrm.m.Keys);
    // assert (mapThruKlon(a.owner, rrm) == b.owner);

    assert klonVMapOK(rrm.m);

    assert klonCanKV(rrm,a,b);
    assert klonVMapOK(klonKV(rrm,a,b).m);



    assert inside(a,rrm.o);
    assert b.fieldModes == a.fieldModes;


//    assert mapThruKlon(a.owner, rrm) == b.owner;
    assert a !in a.owner;
//    assert mapThruVMapKV(a.owner, rrm.m, a, b) == mapThruVMap(a.owner, rm.m);

// assert b.owner == mapThruVMap(a.owner, rm.m);
// assert b.owner == mapThruKlon(a.owner, rm);
// IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner, rm.m, a, b);
// assert (mapThruKlonKV(a.owner, rm, a, b) == b.owner);
// assert (mapThruKlonKV(a.owner, rrm, a, b) == b.owner);

//KJXOWNERS
// assert (mapThruKlon(a.owner, km) == b.owner);

assert a.AMFO == flattenAMFOs(a.owner) + {a};

var amxo := flattenAMFOs(a.owner);
assert  a.AMFO == amxo + {a};
// var other := mapThruKlon(a.owner,km);
// var omxo := mapThruKlon(amxo, km);

///preonditions for mapThruKlonPreservesFlatness3
assert km.calid();
assert a.owner <= km.m.Keys;
assert amxo <= km.m.Keys;
assert amxo == flattenAMFOs(a.owner);
// assert AllTheseOwnersAreFlatOK(amxo);
// assert other == mapThruKlon(a.owner, km);
// assert other == b.owner;  //KJXOWNERS...
// assert  omxo == mapThruKlon(amxo, km);

//  // //assume false;
// return;///FUKOF  //WORKS 26-34s

// mapThruKlonPreservesFlatness3(a.owner, amxo,
//                     other, omxo, km);


// assert  omxo == flattenAMFOs(other);
// assert  AllTheseOwnersAreFlatOK(omxo);

// assert  mapThruKlonKV({a}, rrm, a, b) == {b};
// mapThruKlonKVisOK({a}, rrm, a, b);

assert  km.m[a] == b;
// mapThruKlonSingleton(a, km);

// assert mapThruKlon({a}, klonKV(rrm, a, b)) == {b};
// assert mapThruKlon({a}, km) == {b};
// assert mapThruKlonKV({a}, rrm, a, b) == {b};

assert b.AMFO == flattenAMFOs(b.owner) + {b};

assert a.allExternalOwners() <= km.m.Keys;
assert {a} <=  km.m.Keys;
assert a.AMFO == a.allExternalOwners() + {a};

assert a.AMFO <= km.m.Keys;
//assert b.AMFO == mapThruKlon(a.AMFO, km);

//mapThruKlonPreservesAMFO2(a,b,km);

//    assert mapThruKlon(a.AMFO, km) == b.AMFO;


//    assert mapThruKlonKV(a.AMFO, rrm, a, b) == b.AMFO;



assert km == klonKV(rrm,a,b);
//assert rrm.AreWeNotMen(a, klonKV(rrm,a,b));
assert klonKV(rrm,a,b).AreWeNotMen(a, klonKV(rrm,a,b));
assert km.AreWeNotMen(a, km);
assert km.AreWeNotMen(a, klonKV(rrm,a,b));
AWNMFUCKED(a, km, rrm);
assert rrm.AreWeNotMen(a, klonKV(rrm,a,b));

// mapThruKlonKVisOK(a.AMFO, rrm, a, b);
//assert mapThruKlonKV(a.AMFO, rrm, a, b) == b.AMFO;


/////////////////////////////////////////////////////////
  var xm := rrm.putInside(a,b);
/////////////////////////////////////////////////////////


  assert xm.m == MappingPlusOneKeyValue(rrm.m,a,b);

  assert inside(a, xm.o);
  assert b in xm.ns;
  assert BINNS: b in xm.ns;
  reveal UniqueMapEntry();
  assert (UniqueMapEntry(xm.m,a));

  assert xm.m.Keys >= xm.m.Keys + {a};
  assert xm.m.Values >= xm.m.Values + {b};
  assert COK(b, xm.oHeap+xm.ns);
  assert COKB: COK(b, xm.oHeap+xm.ns);

  MapOKFromCalid(xm);
  assert xm.calid();

  // assert mapThruKlon(a.owner, xm) == b.owner;  //KJXOWNERS
  // assert mapThruKlon(a.AMFO, xm)  == b.AMFO;

  print "Clone_CLone_Clone map updated ", fmtobj(a), ":=", fmtobj(b) ,"\n";



    assert xm.m.Values >= m'.m.Values + {b};
//    assert b.AMFO <= xm.m.Values;  ///TUESDAY14DEC2024
   assert b.AMFO <= xm.oHeap+xm.ns;

//END FUCKOFF
  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   preconditiosn for call of Clone_All_Fields
  /////   /////    /////    /////   /////    /////    /////   /////    /////


  assert xm.calid();
  assert COK(a, xm.oHeap);
  assert COK(b, xm.oHeap+xm.ns);
  reveal COK();
  OwnersValidFromCalid(a,xm);
  OwnersValidFromCalid(b,xm);
  assert a.Valid();
  assert a.AllFieldsAreDeclared();

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

  assert  xm.o     == m'.o;
  assert  xm.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,xm.m);
  assert  xm.m.Keys >= m'.m.Keys + {a};

assert   (m'.oHeap - m'.m.Keys)   >=     (xm.oHeap - xm.m.Keys +{a});

var left :=  (m'.oHeap - m'.m.Keys);
var right := (xm.oHeap - xm.m.Keys +{a});

assert left >= right;
SetGEQisGTorEQ(left,right);
assert ((left >= right) && not(left > right)) ==> (left == right);

if (left >   right) { assert (left decreases to right); }
   else {
      assert left == right;
      assert a.AMFO ==  a.AMFO;
      assert (a.fields.Keys) == (a.fields.Keys);
      assert 15 > 10;
      assert (
    left,   a.AMFO, (a.fields.Keys), 15
  decreases to
    right, a.AMFO, (a.fields.Keys), 10);
   }


assert (
    left,   a.AMFO, (a.fields.Keys), 15
  decreases to
    right, a.AMFO, (a.fields.Keys), 10);


assert (
    (m'.oHeap - m'.m.Keys),      a.AMFO, (a.fields.Keys), 15
  decreases to
    (xm.oHeap - xm.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10)
    by
    {
assert   (m'.oHeap - m'.m.Keys)   >=     (xm.oHeap - xm.m.Keys +{a});
assert    a.AMFO >=  a.AMFO;
assert (a.fields.Keys) >= (a.fields.Keys);
assert  15 > 10;
assert (
    (m'.oHeap - m'.m.Keys),      a.AMFO, (a.fields.Keys), 15
  decreases to
    (xm.oHeap - xm.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10);
    }


assert a.AMFO <= xm.m.Keys;
//assert b.AMFO <= xm.m.Values;  //TUESDAY17DEC2024
assert b.AMFO <= xm.oHeap+xm.ns;


   m := Clone_All_Fields(a,b, xm);

  /////   /////    /////    /////   /////    /////    /////   /////    /////
  /////   /////    /////    /////   /////    /////    /////   /////    /////

  assert m.m.Keys >= xm.m.Keys;
  assert m.m.Values >= xm.m.Values;

  assert m.m.Keys >= m'.m.Keys + {a};
  assert m.m.Values >= m'.m.Values + {b};

  assert b in xm.ns by { reveal BINNS; }
  assert b in m.ns  by { reveal BINNS; }

  assert COK(b, m.oHeap+m.ns) by { reveal COKB; }

  print "Clone_Clone_CLone of ", fmtobj(a), " retuning ", fmtobj(b) ,"\n";

  assert m.m.Values >= m'.m.Values + {b};
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
  //a should be preexisting (in m'.oHeapl); b should be "new" (in m'.ns)

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
  requires a.AMFO <= m'.m.Keys //KJX should be part of some invariant

  requires b in m'.ns
  requires b in m'.m.Values
//  requires b.AMFO <= m'.m.Values //KJX should be part of some invariant - also
  requires b.AMFO <= m'.oHeap+m'.ns

  requires (a in m'.m.Keys) && m'.m[a] == b
  requires m'.o    in m'.oHeap
  requires m'.m.Keys   <= m'.oHeap


    //not sure why I'd need this..
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
  ensures a.AMFO <= m.m.Keys // shoulnd't that be requires

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

  assert klonOwnersAreCompatible(a, b, m') by {
      reveal m'.calid(), m'.calidObjects(), m'.calidOK(), m'.calidMap(), m'.calidSheep();
      assert m'.calidObjects() && m'.calidOK() && m'.calidMap() && m'.calidSheep() && m'.calid();
      assert klonOwnersAreCompatible(a, b, m');
    }

  m := m';

assert m.from(m');
//SPLURGE
assert (m.calid()) by
{
  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  assert m.calidObjects() && m.calidOK() && m.calidMap() && m.calidSheep() && m.calid();
}
assert klonOwnersAreCompatible(a, b, m);
//END SPLURGE



  var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map *variant for decreases clause*

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

  OutgoingReferencesWithinKlonHeapFromCalid(m);
  assert forall x <- m.oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m.oHeap);

  assert a in m.oHeap;
  assert a.Ready();
  assert a.AllOutgoingReferencesWithinThisHeap(m.oHeap);

  var ofv := COKat(a,n,m.oHeap);

  label B3:
  assert m'.calid() by { reveal MPRIME; }



  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
  var rfv, rm := Clone_Via_Map(ofv, m);
  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

  label B3X:
  assert rm.calid();
  assert rm.from(m);
  assert klonVMapOK(rm.m);
  assert rm.m[ofv] == rfv;

  assert RFVCOK: COK(rfv, rm.oHeap+rm.ns) by {
    assert rfv in rm.m.Values;
    rm.calidOKFromCalid();
    assert CallOK(rm.m.Values, rm.oHeap+rm.ns);
    COKfromCallOK(rfv, rm.m.Values, rm.oHeap+rm.ns);
  }

  m := rm;

  //SPLURGE
  assert (m.calid()) by
  {
    reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
    assert m.calidObjects() && m.calidOK() && m.calidMap() && m.calidSheep() && m.calid();
  }
  //END SPLURGE

  assert unchanged(m'.ns);

//   assert m'.calid() by { reveal MPRIME; }
//
//   assert unchanged@B3(m'.oHeap);


  assert rfv in  m.m.Values;
  // assert rfv in  m.oHeap+m.ns;   //let's see if we need these bits.
  // assert COK(rfv,m.oHeap+m.ns);

//////ensure cloned field is refOK ////////////

  assert m.calid();
  assert {a,ofv} <= m.m.Keys;
  assert b == m.m[a];
  assert rfv == m.m[ofv];

  assert a in m.m.Keys;
  assert b == m.m[a];

  klonOwnersAreCompatibleWider(a,b,m',m);
  assert klonOwnersAreCompatible(a, b, m);
  assert klonOwnersAreCompatible(ofv, rfv, m);
  assert refOK(a,ofv);

  // assert m.boundsNestingOK(a, m.oHeap);
  // assert m.boundsNestingOK(b, m.oHeap+m.ns);
  // assert (b.AMFO >= b.AMFB >= a.AMFB);
  //
klonFieldsAreCompatible(a,ofv,b,rfv,m);
//
//   assert refOK(a, ofv);
//
// if (outside(ofv,m.o)) {
// //
// //
//
//           assert
//             (&& klonOwnersAreCompatible(a, b, m)
//              && klonOwnersAreCompatible(ofv, rfv, m))
//           by {
//
//
//               assert klonAllOwnersAreCompatible(m);
//               assert b == m.m[a];
//               assert klonOwnersAreCompatible(a, b, m);
//               assert rfv == m.m[ofv];
//               assert klonOwnersAreCompatible(ofv, rfv, m);
//           }
//
//
//   assert (b.AMFO >= b.AMFB >= a.AMFB);
//   assert (rfv.AMFO >= rfv.AMFB >= ofv.AMFB);
//
//   assert refOK(a, ofv);
//   assert boundInsideOwner(a,ofv) || directlyInside(ofv,a);
//
//   if (boundInsideOwner(a,ofv)) {
//       assert a.AMFB >= (ofv.AMFO - {ofv});
//
//       assert b.AMFB >= (rfv.AMFO - {rfv});
//       assert boundInsideOwner(b,rfv);
//   } else {
//       assert directlyInside(ofv,a);
//       assert a.AMFO == (ofv.AMFO - {ofv});
//
//
//       assert b.AMFO == (rfv.AMFO - {rfv});
//       assert directlyInside(rfv,b);
//   }
//
//   assert boundInsideOwner(b,rfv) || directlyInside(rfv,b);
//   assert refOK(b, rfv);
//
// }//end outside case
//
//
//
//   assert boundInsideOwner(a, ofv) || directlyInside(ofv,a);
//   // mapThruKlonPreservesBoundInsideOwner(a, ofv, b, rfv, m);  //KJXFRIDAY13THK
// //  assert klonRefOK(a, ofv, b, rfv, m);
//
//   assert boundInsideOwner(b, rfv) || directlyInside(rfv, b);

  assert refOK(b, rfv);

//////END ensure cloned field is refOK ////////////



print "ASSUMING ASSIGNMENT COMPATIBLE\n";
        assume AssignmentCompatible(b, b.fieldModes[n], rfv);
print "ASSUMING ASSIGNMENT COMPATIBLE\n";


//   assert AssignmentCompatible(b, b.fieldModes[n], rfv)
//   by {
//     // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//
//     assert b.fieldModes[n] == a.fieldModes[n];
//
//     assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]) by
//     {
//       reveal COK();
//       assert COK(a, m.oHeap);
//       assert a.Valid();
//       assert a.AllFieldsContentsConsistentWithTheirDeclaration();
//       assert forall n <- a.fields.Keys :: AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
//       assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
//     }
//
//
//
//     match (b.fieldModes[n]) {
//       case Evil =>
//         assert b.fieldModes[n] == Evil;
//         EVILisCompatibleWithAnything(b,rfv);
//         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//
//       case Rep | Owned(_) | Loaned(_) =>
//         assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
//         assert ofv == a.fields[n];
//      //   assert ofv.owner == a; //KJX what should this be>?
//         assert b == m.m[a];
//         assert rfv == m.m[ofv];
//      //   assert b == rfv.owner;
//         // assert b == m.m[a.fields[n].owner];
//         // assert b == rfv.owner;
//         // mapThruKlonPreservesInside(ofv,a, rfv, b, m);   //KJXFRIDAY13TH
//         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//
//       case Peer =>
//         assert AssignmentCompatible(a, a.fieldModes[n], ofv);
//         assert a.owner == ofv.owner;
//
//
//           assert COK(a, m.oHeap);
//           RVfromCOK(a, m.oHeap);
//           assert a.OwnersValid();
//           assert a.owner <= a.AMFO <= m.m.Keys;
//
//           assert klonVMapOK(m.m);
//           assert m.m[a] == b;
//           // assert (mapThruKlon(a.owner, m) == b.owner);  //KJXOWNERS mapthru KLon.
//           // assert m.m[ofv] == rfv;
//           // assert mapThruKlon(ofv.owner, m) == rfv.owner;  //KJXOWNERS
//
//           assert b.owner == rfv.owner; //WORK THE FOKKA?
//
//           //assume b.owner == rfv.owner;   //KJXOWNERS
//
//         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//
//       case Borrow(pp,bb,nn,ff) =>
//         assert refOK(a,a.fields[n]);
//         assert refOK(b,rfv);
//         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//     }



    // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
    // }




  assert m.calid();

  assert b in m.ns;

assert (b !in m.oHeap) by {

  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
  assert m.calidObjects() && m.calidOK() && m.calidMap() && m.calidSheep() && m.calid();

    bNotInoHeap(b,m);
    }

  label B4:

  assert m.calidOK() by { reveal m.calid(); }
  assert m'.calid() by { reveal MPRIME; }
  assert m.calid() by {  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep(); }


  assert COK(b, rm.oHeap+rm.ns) by
  {
    assert b in m'.ns;
    assert b in m.ns;
    assert COK(b, m'.oHeap+m'.ns);
    assert m'.ns <= m.ns;
    COKWiderContext2(b,m'.oHeap+m'.ns,m.oHeap+m.ns);
    assert COK(b, m.oHeap+m.ns);
  }

assert COKB4: COK(b, rm.oHeap+rm.ns);

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



  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

//  b.fields := b.fields[n := rfv];


  assert COK(rfv, m.oHeap+m.ns) by { reveal RFVCOK; }
  m.COKput(b, m.oHeap+m.ns, n, rfv);
  assert b.fields == b.fields[n := rfv];
  assert COK(b, m.oHeap+m.ns);

  // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //


  assert unchanged(m'.ns - {b});

  assert CallOK(m.m.Values-{b}, m.oHeap+m.ns);
  assert CallOK(m.ns-{b}, m.oHeap+m.ns);
  assert Call_NOB: CallOK(m.ns-{b}, m.oHeap+m.ns);


  assert m.m[ofv] == rfv;
  assert rfv in m.m.Values;
  assert rfv in m.oHeap+m.ns;


  if (b != rfv) {

    assert rfv in (m.oHeap+m.ns);
    if (rfv in m.oHeap)
       {
        assert unchanged(m.oHeap);
        assert unchanged(rfv);
       } else {
        assert rfv !in m.oHeap;
        assert rfv in m.ns;
        assert unchanged(m'.ns - {b});
        assert rfv != b;
        assert unchanged@B3X(rfv);
       }
    assert unchanged@B3X(rfv);
    assert COK(rfv, rm.oHeap+rm.ns) by { reveal RFVCOK; }

//    assert rm == m;
//    assert rm.from(m);  //HOW ODD

    // m'.calidOKFromCalid();
    // COKfromCallOK(rfv,m.m.Values, m.oHeap+m.ns);
    // assert COK(rfv,m.oHeap+m.ns);

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
  //  assert ((m.ns-{b}) + {b}) == m.ns;   what the FUCK is this doing anyway?

    assert b in m'.m.Values;
    assert b in  m.m.Values;

    assert m.m.Values <= m.oHeap+m.ns by { reveal m.calid(); reveal m.calidOK(); }

    assert COK(b, m.oHeap+m.ns);
    assert b in  m.oHeap+m.ns by { reveal COK(); }
    CallOKfromCOK(b, m.oHeap+m.ns);
    assert CallOK({b}, m.oHeap+m.ns);
    assert CallOK(m.ns-{b}, m.oHeap+m.ns);

    if (b in m.ns) {
      assert b in m.ns;
      assert COK(b, m.oHeap+m.ns);

//      CallOKWiderFocus(m.ns-{b}, {b}, m.oHeap+m.ns);

      reveal COK(), CallOK();
      assert forall o <- (m.ns-{b}) :: COK(o, m.oHeap+m.ns);
      assert forall o <- ({b}) ::  COK(o, m.oHeap+m.ns);
      assert forall o <- ((m.ns-{b})+{b}) :: COK(o, m.oHeap+m.ns);
      assert forall o <- (m.ns) :: COK(o, m.oHeap+m.ns);
      assert CallOK(m.ns, m.oHeap+m.ns);
    } else {
      assert b !in m.ns;
      assert CallOK(m.ns-{b}, m.oHeap+m.ns) by { reveal Call_NOB; }
      assert (m.ns-{b}) == m.ns;
      assert CallOK(m.ns, m.oHeap+m.ns);
    }


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

// IHasCalidObjects(m);
//
// assert klonVMapOK(m.m);
//
// IHasCalidMap(m);


  // requires AllMapEntriesAreUnique(r.m)
  // requires klonVMapOK(r.m)
  // requires (forall x <- r.m.Keys :: (not(inside(x,r.o)) ==> (r.m[x] == x)))
  // requires (forall x <- r.m.Keys, oo <- x.AMFO :: r.m[oo] in r.m[x].AMFO)

  assert m.calid() by
  {
    reveal m.calid();
    reveal m.calidObjects();
    reveal m.calidOK();
    reveal m.calidMap();
    reveal m.calidSheep();

    assert m.calidObjects();
    assert m.calidOK();


    assert AllMapEntriesAreUnique(m.m);
    assert klonVMapOK(m.m);
    assert (forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.m[x] == x)));
  ///  assert (forall x <- m.m.Keys, oo <- x.AMFO :: m.m[oo] in m.m[x].AMFO); ///KJXFRIDAY13TH


    assert klonAllOwnersAreCompatible(m);
    assert klonAllRefsOK(m);

    assert m.calidMap();/////////////////////////

    assert m.m.Keys == m.m.Keys;
    reveal m.AreWeNotMen();
    assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);

    assert (forall x <- m.m.Keys :: m.AreWeNotMen(x, m));
    assert (forall x <- m.m.Keys :: x.fieldModes == m.m[x].fieldModes);
    assert AllMapEntriesAreUnique(m.m);

IHasCalidSheep(m);

    assert m.calidSheep();/////////////////////////

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

  MapOKFromCalid(m);
  assert klonVMapOK(m.m);

} //end Clone: /_Field_Map




function mapThruKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  //image of os under klon mapping m
  //currently doesn't require calid, to avoid circular reasonings
  //but can reason through calid. which is probalby bad,really
  //be bettter to split off as a lemma...
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields, m.ns`fieldModes
//requires m.calid()  (does it or doesn't it?)
  requires os <= m.m.Keys

  ensures m.calid() ==> (r  <= m.m.Values <= (m.oHeap + m.ns))  //Hmm. not great but...
  ensures m.calid() ==> (CallOK(r, (m.oHeap + m.ns))) //ditto. or should they be lemmas..?
{
  var r := set o <- os :: m.m[o];

  reveal m.calid(), m.calidOK();
  assert m.calid() ==> (r  <= m.m.Values <= (m.oHeap + m.ns));

  reveal COK(), CallOK();
  assert m.calid() ==> (CallOK(r, (m.oHeap + m.ns)));

  r
}

//LEMMA  given a calid? Klon,  and that we canKV the fuyckedr,
//then reult wil lbe calid, or if not calid, at leaset fucking klonVMapOK or whatever it is...
//not sure why this is up here not down the other end


      // assert mapThruKlonKV(k.AMFO, this, k, v) == v.AMFO;

      // assert (forall x <- m.Keys     :: mapThruKlon(x.AMFO, this) == m[x].AMFO);
      // assert (forall x <- m.Keys     :: mapThruKlonKV(x.AMFO, this, k, v) == m[x].AMFO);
      // assert (forall x <- m.Keys+{k} :: mapThruKlonKV(x.AMFO, this, k, v) == m[x].AMFO);
      // assert rv.m.Keys == m.Keys + {k};
      // assert rv == klonKV(this,k,v);
      // assert (forall x <- rv.m.Keys  :: mapThruKlon(x.AMFO, rv)   == rv.m[x].AMFO);




//this one is more vmap than klon...
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







lemma KlonVMapOKfromCalid(m : Klon)
  requires m.calid()
  ensures  klonVMapOK(m.m)
  {
    reveal m.calid();
    reveal m.calidMap();

    assert m.calid();
    assert klonVMapOK(m.m);
  }



 predicate  klonOwnersAreCompatible(o : Object, c : Object, m : Klon)
  requires o in m.m.Keys
  requires c == m.m[o]
  //the
  reads m.oHeap`fields, m.oHeap`fieldModes
  reads m.ns`fields,    m.ns`fieldModes
  reads o`fields, o`fieldModes
  reads c`fields, c`fieldModes

{
  && m.boundsNestingOK(o, m.oHeap)
  && m.boundsNestingOK(c, m.oHeap+m.ns)

  && (c.AMFO >= c.AMFB >= o.AMFB)
}


predicate klonAllOwnersAreCompatible( m : Klon, ks: set<Object> := m.m. Keys)
//
requires ks <= m.m. Keys
reads m.oHeap`fields,      m.oHeap`fieldModes
reads m.ns`fields,         m.ns`fieldModes
reads m.m.Keys`fields,     m.m.Keys`fieldModes
reads m.m.Values`fields,   m.m.Values`fieldModes
  {
    forall o <- ks :: klonOwnersAreCompatible(o,m.m[o],m)
  }


lemma  klonOwnersAreCompatibleWider(o : Object, c : Object, m' : Klon, m : Klon)
  requires o in m'.m.Keys
  requires c == m'.m[o]
  requires klonOwnersAreCompatible(o, c, m')
  //requires m'.calid()
  //requires m.from(m')
  requires mapGEQ(m.m, m'.m)
  requires m.o     == m'.o
  requires m.oHeap == m'.oHeap
  requires m.ns    >= m'.ns
  ensures  klonOwnersAreCompatible(o, c, m)
{
  assert
      && m.boundsNestingOK(o, m'.oHeap)
      && m.boundsNestingOK(c, m'.oHeap+m'.ns)
      && (c.AMFO >= c.AMFB >= o.AMFB)
      ;

    m.widerBoundsNest(o, m'.oHeap, m.oHeap);
    m.widerBoundsNest(c, m'.oHeap+m'.ns, m.oHeap+m.ns);

  assert
      && m.boundsNestingOK(o, m.oHeap)
      && m.boundsNestingOK(c, m.oHeap+m.ns)
      && (c.AMFO >= c.AMFB >= o.AMFB)
      ;

  assert klonOwnersAreCompatible(o, c, m);
}

lemma klonFieldsAreCompatible(of : Object, ot : Object, cf : Object, ct: Object, m : Klon)
{}

lemma klonSameOwnersAreCompatible(k : Object, v : Object, m1 : Klon)
{}






predicate klonAllRefsOK(m : Klon) { wexford2(m) }



lemma klonAllRefsKVOK(k : Object, v : Object, m' : Klon, m : Klon)
  requires klonAllRefsOK(m')
  //requires m'.calid()
  requires klonCanKV(m',k,v)
  requires m == klonKV(m',k,v)
  requires m.m.Keys == m'.m.Keys+{k}
  requires m.m.Values == m'.m.Values+{v}
  requires m.m[k] == v
  requires m.m == m'.m[k:=v]


  //this one of course...
  //  requires forall ot <- (m'.m.Keys + {k}) ::  klonRefOK(k,ot,v,m.m[ot],m)

  ensures   klonAllRefsOK(m)
{
  assert k !in m'.m.Keys;

  assert mapGEQ(m.m,m'.m);

//   assert  forall of <- m'.m.Keys, ot <- m'.m.Keys ::
//      var cf := m'.m[of];
//      var ct := m'.m[ot];
//       false; //TODO
// //     klonRefOK(of,ot,cf,ct,m');

  assert (forall of <- m'.m.Keys, ot <- m'.m.Keys ::
            (var cf := m'.m[of];  assert cf == m.m[of];
            (var ct := m'.m[ot];  assert ct == m.m[ot];
              false))); //TODO
  //   klonRefOK(of,ot,cf,ct,m) == klonRefOK(of,ot,cf,ct,m');

//NEED EXISTENTIONALITY HERE   TODO
//very much so!


//
//   assert forall of <- m.m.Keys, ot <- m.m.Keys ::
//      var cf := m.m[of];
//      var ct := m.m[ot];
//
//     if ((of in m'.m.Keys) && (ot in m'.m.Keys))
//        then  (klonRefOK(of,ot,cf,ct,m'))
//        else  (false);
//
//
//
//   assert forall of <- m.m.Keys, ot <- m.m.Keys ::
//      var cf := m.m[of];
//      var ct := m.m[ot];
//      klonRefOK(of,ot,cf,ct,m);
}






lemma bixy(a : Object, b : Object, c : Object, m : Klon)
  requires a.Ready()
  requires b.Ready()
  requires c.Ready()

//  requires forall o <- {a, b, c} :: o.Ready()  //doesn't wwork!

  requires refBI(a,b)

  ensures  (a.AMFO > a.AMFX >= a.AMFB)
  ensures  (b.AMFO > b.AMFX >= b.AMFB)
  ensures  a.AMFB >= b.AMFX
  ensures  (a.AMFO > a.AMFX >= a.AMFB >= b.AMFX >= b.AMFB)
  ensures  a.AMFB >= b.AMFB

  //  Inside3(a,b,c);
{}

lemma trexy(a : Object, b : Object, c : Object, m : Klon)
  requires a.Ready()
  requires b.Ready()
  requires c.Ready()

  requires refBI(a,b)
  requires refBI(b,c)
  ensures  refBI(a,c)
{}


predicate wexy(of : Object, ot : Object, cf : Object, ct: Object, m : Klon) : ( rv : bool )
//note doesnt requrie Valid???
//  requires wexford3(m)
  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct

  requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))


  requires (of != cf) ==> (cf.AMFO >= m.c_amfo)
  requires (ot != ct) ==> (ct.AMFO >= m.c_amfo)


  ensures rv == (refOK(of,ot) ==> refOK(cf,ct))
{

  // 25DEC 2024 - starting on the 2x2 version inside/outside of ,ot cases
  //
  if (not(of.AMFO >= m.o_amfo))
    then //from outside
      (if (not(ot.AMFO >= m.o_amfo)) then (
        //both outside
        assert (not(of.AMFO >= m.o_amfo)) && (not(ot.AMFO >= m.o_amfo));
        assert of == cf;
        assert ot == ct;
        refOK(of,ot) ==> refOK(cf,ct)
      ) else (
        //from outside to inside...
        assert (not(of.AMFO >= m.o_amfo)) && (ot.AMFO >= m.o_amfo);
        assert of == cf;
        assert ct.AMFO >= m.c_amfo;
        refOK(of,ot) ==> refOK(cf,ct)))
    else //from inside
      (if (not(ot.AMFO >= m.o_amfo)) then (
        //from inside to outside
        assert (of.AMFO >= m.o_amfo) && (not(ot.AMFO >= m.o_amfo));
        assert cf.AMFO >= m.c_amfo;
        assert ot == ct;
        refOK(of,ot) ==> refOK(cf,ct)
      ) else (
        //both inside
        assert (of.AMFO >= m.o_amfo) && (ot.AMFO >= m.o_amfo);
        assert cf.AMFO >= m.c_amfo;
        assert ct.AMFO >= m.c_amfo;
        refOK(of,ot) ==> refOK(cf,ct)))
}

predicate dexy(of : Object, ot : Object, cf : Object, ct: Object, m : Klon) : ( rv : bool )
//  requires wexford3(m)
/// HMM doesit still work?
// agan doesn't need Valid??
  requires {of, ot} <= m.m.Keys
  requires m.m[of] == cf
  requires m.m[ot] == ct

  requires (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) <==> (m.m[x] == x)))

  ensures rv == (refOK(of,ot) ==> refOK(cf,ct))
{

  // 25DEC 2024 - version done by case analysis of the refOK(of,ot)
  //

  if (of == ot) then (
    assert refOK(of,ot);
    refOK(cf,ct)) else (
  if (refDI(of,ot)) then (
    assert refOK(of,ot);
    refOK(cf,ct)) else (
  if (refBI(of,ot)) then (
    assert refOK(of,ot);
    refOK(cf,ct)
  ) else (
    assert not(refOK(of,ot));
    true)))
}






predicate wexford4(m : Klon)
  requires wexford3(m)
{
  && (forall i <- m.m.Keys, j <- m.m.Keys :: wexy(i,j,m.m[i],m.m[j],m))
}

predicate wexford3(m : Klon)
{
  && (m.m.Keys   <= m.oHeap)
  && (m.m.Values <= m.oHeap)
  && (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) ==> (m.m[x] == x)))


  && (forall x <- m.m.Keys ::
      (if (x.AMFO >= m.o_amfo)
        then ((m.m[x] != x) && (m.m[x].AMFO >= m.c_amfo))
        else ((m.m[x] == x))))

//  && (forall i <- m.m.Keys, j <- m.m.Keys :: wexy(i,j,m.m[i],m.m[j],m))

}


predicate wexford2(m : Klon)
{
  && (m.m.Keys   <= m.oHeap)
  && (m.m.Values <= m.oHeap)
  && (forall x <- m.m.Keys :: (not(x.AMFO >= m.o_amfo) ==> (m.m[x] == x)))
  && (forall i <- m.m.Keys, j <- m.m.Keys :: refOK(i,j) ==> refOK(m.m[i],m.m[j]))
}



predicate wexford(m : Klon)
{
    forall i <- m.m.Keys, j <- m.m.Keys :: refOK(i,j) ==> refOK(m.m[i],m.m[j])

}

predicate waterford(m : Klon)
{
    forall i <- m.m.Keys, j <- m.m.Keys | refOK(i,j) :: refOK(m.m[i],m.m[j])

}

lemma wexwater(m : Klon)
  ensures wexford(m) == waterford(m)
{}




// lemma klonFieldsAreCompatible(of : Object, ot : Object, cf : Object, ct: Object, m : Klon)
//   //can of->ot clone to cf-ct
// //  requires m.calid()///doesnt work cos this is kinda pointless...
//   requires {of,ot} <= m.m.Keys
//   requires cf == m.m[of]
//   requires ct == m.m[ot]
//
//   requires klonOwnersAreCompatible(of, cf, m)
//   requires klonOwnersAreCompatible(ot, ct, m)
//   requires refOK(of,ot)
//   ensures  refOK(cf,ct)
// {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidOK();
//               assert m.calidOK();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               reveal m.calidMap();
//               assert m.calidMap();
// }






































lemma IHasCalid(r : Klon)
    requires r.calidObjects()
    requires r.calidOK()
    requires r.calidMap()
    requires r.calidSheep()

    ensures  r.calid()
{
    reveal r.calid();
    assert r.calid();
}

lemma IHasCalidObjects(r : Klon)
    requires r.o in r.oHeap       ///
    requires r.m.Keys <= r.oHeap
    requires r.ns !! r.oHeap       ////
    requires r.m.Values <= r.ns + r.oHeap
    requires r.ns <= r.m.Values

    ensures  r.calidObjects()
{
    reveal r.calidObjects();
}


lemma IHasCalidOK(r : Klon)
    requires (r.o in r.oHeap)
    requires (r.m.Keys <= r.oHeap)
    requires (r.m.Values <= r.oHeap+r.ns)
    requires COK(r.o, r.oHeap)
    requires CallOK(r.oHeap)
    requires CallOK(r.m.Keys, r.oHeap)
    requires CallOK(r.m.Values, r.oHeap+r.ns)
    requires CallOK(r.ns, r.oHeap+r.ns)
    requires (forall x <- r.oHeap :: (x.Ready() && x.AllOutgoingReferencesWithinThisHeap(r.oHeap)))

    ensures  r.calidOK()
{

    reveal r.calidOK();
}

lemma IHasCalidMap(r : Klon)
  requires r.calidOK()
  requires r.calidObjects()
  requires AllMapEntriesAreUnique(r.m)
  requires klonVMapOK(r.m)
  requires (forall x <- r.m.Keys :: (not(inside(x,r.o)) ==> (r.m[x] == x)))

  requires (forall x <- r.m.Keys :: r.boundsNestingOK(x, r.oHeap))
  requires (forall x <- r.m.Keys :: r.boundsNestingOK(r.m[x], r.oHeap+r.ns))
  requires (forall x <- r.m.Keys :: r.fieldMappingsOK(x, r.m[x], r.m.Keys))

  requires klonAllRefsOK(r)
  requires klonAllOwnersAreCompatible(r)
  // requires  && (forall x <- r.m.Keys ::
  //       && r.boundsNestingOK(x, r.oHeap)
  //       && r.boundsNestingOK(r.m[x], r.oHeap+r.ns)
  //       && r.fieldMappingsOK(x, r.m[x], r.m.Keys))


  // requires (forall x <- r.m.Keys, oo <- x.owner :: r.m[oo] in r.m[x].owner) //KJXOWNERS
  // requires (forall x <- r.m.Keys, oo <- x.AMFO  :: r.m[oo] in r.m[x].AMFO)

  ensures  r.calidMap()
  {
        reveal r.calidObjects(); assert r.calidObjects();
        reveal r.calidOK(); assert r.calidOK();

        assert
          && (forall x <- r.m.Keys :: r.boundsNestingOK(x, r.oHeap))
          && (forall x <- r.m.Keys :: r.boundsNestingOK(r.m[x], r.oHeap+r.ns))
          && (forall x <- r.m.Keys :: r.fieldMappingsOK(x, r.m[x], r.m.Keys))
          ;

        assert
          && klonAllRefsOK(r)
          && klonAllOwnersAreCompatible(r)
          && AllMapEntriesAreUnique(r.m)
          && klonVMapOK(r.m) // potentiall should expand this out?
          && (forall x <- r.m.Keys :: (not(inside(x,r.o)) ==> (r.m[x] == x)))
          // && (forall x <- r.m.Keys, oo <- x.owner :: r.m[oo] in r.m[x].owner) //KJXOWNERS
          // && (forall x <- r.m.Keys, oo <- x.AMFO  :: r.m[oo] in r.m[x].AMFO)
          ;
        reveal r.calidMap();
        assert r.calidMap();
    }


lemma IHasCalidSheep(r : Klon)
  requires r.calidObjects() && r.calidOK()// && calidMap()
  requires (forall x <- r.m.Keys :: r.AreWeNotMen(x, r))
  requires (forall x <- r.m.Keys :: x.fieldModes == r.m[x].fieldModes)
  requires AllMapEntriesAreUnique(r.m)

  ensures r.calidSheep()
{
  reveal r.calidObjects(); assert r.calidObjects();
  reveal r.calidOK(); assert r.calidOK();
  reveal r.AreWeNotMen();

  reveal r.calidSheep();
  assert r.calidSheep();
}





method Clone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)
  //adds all thers owners of a into the map
//31mins
  decreases (m'.oHeap - m'.m.Keys + {a}), a.AMFO, (a.fields.Keys), 12

  requires a !in m'.m.Keys //mustn't have cloned a yet...
  requires COK(a, m'.oHeap)
  requires m'.calid()

  ensures  m.calid()
  //ensures  a !in m.m.Keys //can't ensures this cos an onwer could have a pointer to "a"

  ensures m.from(m')
  ensures a.owner <= m.m.Keys
  ensures a.allExternalOwners() <= m.m.Keys
  ensures mapThruKlon(a.allExternalOwners(),m) <= m.m.Values
     //the above should be OK because it's bascially tautological
  modifies {}
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

  var MX := a.owner - xm.m.Keys;


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
      assert a.allExternalOwners() <= m.m.Keys;

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

    assert MX <= (a.owner - xm.m.Keys);

    assert xm.from(m');

    assert xm == rm;
  } // end loop MX

  m := xm;

  assert a.owner <= m.m.Keys;
  AMFOsFromOwnersFromCalid(a,m);
  assert a.allExternalOwners() <= m.m.Keys;
}










lemma MapOKFromCalid(m : Klon)
  requires m.calid()
  ensures  klonVMapOK(m.m)
{  ////
  reveal m.calid();
  reveal m.calidMap();
}
lemma KlonKVExtendsTo(c : Klon, k : Object, v : Object, d : Klon)
  requires klonVMapOK(c.m)
  requires klonCanKV(c, k, v)
  requires d == klonKV(c, k, v)
  ensures  k !in c.m.Keys
  ensures  forall i <- c.m.Keys :: i in d.m.Keys
  ensures  forall i <- c.m.Keys :: c.m[i] == d.m[i]
  ensures  d.m[k] == v
  ensures  klonVMapOK(d.m)
{
  assert klonVMapOK(d.m);
}




lemma OutsidersArentMapValues(a : Object, m : Klon)
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




lemma OwnersValidFromCalid(a : Object, m : Klon)
  requires m.calid()
  requires
    || COK(a, m.oHeap)
    || COK(a, m.oHeap+m.ns)
    || (CallOK(m.oHeap) && (a in m.oHeap))
    || (CallOK(m.m.Keys, m.oHeap) && (a in m.m.Keys))
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
    || (COK(a, m.oHeap+m.ns) && a.Ready())
    || (CallOK(m.oHeap) && (a in m.oHeap) && a.Ready())
    || (CallOK(m.m.Keys, m.oHeap) && (a in m.m.Keys) && a.Ready())
    || (CallOK(m.m.Keys, m.oHeap+m.ns) && (a in m.m.Keys) && a.Ready());

  assert a.Ready();
  assert a.OwnersValid();
}

lemma OutgoingReferencesWithinKlonHeapFromCalid(m : Klon)
   requires m.calid()
   ensures  forall x <- m.oHeap :: (x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m.oHeap))
{
   reveal m.calid();   assert m.calid();
   reveal m.calidOK(); assert m.calidOK();
   assert forall x <- m.oHeap :: (x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m.oHeap));
}


lemma AMFOsFromOwnersFromCalid(a : Object, m : Klon)
  //better name woiuld be: all All_Exterbal_Owners_Are_Keys
  // given a.owner <= keys of m (and other stuff)
  // all a's AMFOS are ready and valid and in the keys of m
  // (does NOT require a itself is in keys of m)
  requires m.calid()

  requires
    || COK(a, m.oHeap)
    || (CallOK(m.oHeap) && (a in m.oHeap))
    || (CallOK(m.m.Keys, m.oHeap) && (a in m.m.Keys))
    || (CallOK(m.m.Keys, m.oHeap+m.ns) && (a in m.m.Keys))

  requires a.owner                <= m.m.Keys
  ensures  a.allExternalOwners()  <= m.m.Keys

  ensures  (a in m.m.Keys) ==> (a.AMFO <= m.m.Keys)
{
    OwnersValidFromCalid(a, m);

     assert m.calid();
     assert (forall k <- m.m.Keys :: k.AMFO <= m.m.Keys)
     //(forall k <- m.m.Keys :: {k} <= k.owner <= k.AMFO <= m.m.Keys)
     //  //KJX this this above nested subset chain is beautiful...
     //BUT IT"S CRAP CRAP cos {k} !in k.owner;  and mauy not be in m,.m,.Keys at this point.
       by {
        reveal m.calid();
        assert m.calid();
        reveal m.calidMap();
        assert m.calidMap();
        assert klonVMapOK(m.m);
      //  assert forall k <- m.m.Keys ::  k.allExternalOwners() == k.AMFO - {a};
        assert (forall k <- m.m.Keys :: k.AMFO <= m.m.Keys);
    //    assert  (forall k <- m.m.Keys :: k.owner <= k.allExternalOwners()  <= m.m.Keys);
     }

     assert a.owner <= m.m.Keys;
     assert flattenAMFOs(a.owner) <= a.AMFO;
     assert flattenAMFOs(a.owner) <= m.m.Keys;
     assert a.allExternalOwners() <= m.m.Keys;

    //keeping this in MAKES THINGS SLOWER!
    // if (a in m.m.Keys) {
    //     assert a.allExternalOwners()          <= m.m.Keys;
    //     assert {a}                            <= m.m.Keys;
    //     assert (a.allExternalOwners() + {a})  <= m.m.Keys;
    //     assert a.allExternalOwners() + {a}    == a.AMFO;
    //     assert a.AMFO                         <= m.m.Keys;
    // }
    //
    // assert

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



















// lemma PsychoBigFoot(os : set<Object>, context : set<Object> := os, m : Klon)

//    requires m.calid()
//    requires os <= m.m.Keys
//    requires context <= m.m.Keys
//    requires os <= context
//    requires OrigBigfoot(os,context)

//    ensures  m.calid()
//    ensures  os <= m.m.Keys
//    ensures  context <= m.m.Keys
//    ensures  os <= context
//    ensures  OrigBigfoot(mapThruKlon(os,m),mapThruKlon(context,m))
// {
//     assert (os <= context);
//     assert (forall o <- os ::  o.AMFO <=  context);
//     assert OrigBigfoot(os,context);

//     reveal m.calid(); assert m.calid();
//     reveal m.calidObjects(); assert m.calidObjects();
//     reveal m.calidOK(); assert m.calidOK();
//     reveal m.calidMap(); assert m.calidMap();
//     reveal m.calidSheep(), m.calidSheep2();
//     assert m.calidSheep();
//     assert klonVMapOK(m.m);

// assert  (forall x <- m.m.Keys ::
//   (set oo <- x.AMFO :: m.m[oo]) == m.m[x].AMFO); //NEW BIT


//    assert os <= m.m.Keys;
//    assert os <= m.m.Keys  ;
//    assert context <= m.m.Keys;
//    assert context <= m.m.Keys  ;
//    assert os <= context;
//    assert OrigBigfoot(os,context);


// assert (forall o <- os :: o.AMFO <=  context);

//    assert mapThruKlon(os, m) <=  mapThruKlon(context, m);
//    assert m.calid();


// BothSidesNow(m.m);
// mapThruKlonPreservesSubsets(os, context, m);
// mapThruKlonPreservesAMFO(os, context, m);

// forall o <- os ensures (
//       mapThruKlon(o.AMFO, m) <= mapThruKlon(context, m))
//     {
//       assert o.AMFO <= context;
//       mapThruKlonPreservesSubsets(o.AMFO, context, m);
//       assert mapThruKlon(o.AMFO, m) == m.m[o].AMFO;
//     }


// forall r <- mapThruKlon(os, m) ensures (
//       r.AMFO <= mapThruKlon(context, m)) {
//          mapThruKlonPreservesSubsets(os, context, m);
//          mapThruKlonPreservesAMFO(os, context, m);
//          assert r.AMFO <= mapThruKlon(context, m);
//       }

//    assert (forall o <- mapThruKlon(os, m)  ::  o.AMFO <=   mapThruKlon(context, m));


// assert  OrigBigfoot(mapThruKlon(os,m),mapThruKlon(context,m));

// }




































/////     /////     /////     /////     /////     /////     /////
    /////     /////     /////     /////     /////     /////     /////
/////     /////     /////     /////     /////     /////     /////
    /////     /////     /////     /////     /////     /////     /////



// using "nu" instead...
//
// function setif<E(==)>(q : bool, e : E) : set<E>
// {
//   if (q) then {e} else {}
// }






lemma NoKeyNoProblems(ks : set<Object>, m' : Klon, k : Object, v : Object)
    requires m'.calid()
    requires ks <= m'.m.Keys
    requires k !in m'.m.Keys
    requires k !in ks
    requires v !in m'.m.Values
    requires canVMapKV(m'.m, k, v)     /// rather than klonCanKV
    ensures  mapThruVMapKV(ks, m'.m, k, v) == mapThruVMap(ks, m'.m)
  //  ensures  mapThruKlonKV(ks, m', k, v) == mapThruKlon(ks, m')
    {
assert canVMapKV(m'.m, k, v);
IfImNotTheExtraKeyTheUnderlyingMapIsFine(ks, m'.m, k, v);
assert mapThruVMapKV(ks, m'.m, k, v) == mapThruVMap(ks, m'.m);
///  mapThruVMapIsMapThruKlon(ks, m', mapThruVMap(ks,  m'.m));
assert mapThruVMap(ks, m'.m) == mapThruKlon(ks, m');
//assert mapThruKlonKV(ks, m', k, v) == mapThruKlon(ks, m');

    }


lemma TargetOwnersReallyAreOK(b : Object, m : Klon)
  requires m.calid()
//  requires COK(b, m.m.Values)

  requires COK(b, m.oHeap+m.ns)

  // ensures  b.AMFO  <= m.m.Values
  // ensures  b.AMFB  <= m.m.Values
  // ensures  b.owner <= m.m.Values

  ensures  b.AMFO  <= m.oHeap+m.ns
  ensures  b.AMFB  <= m.oHeap+m.ns
  ensures  b.owner <= m.oHeap+m.ns
{
//  assume b.AMFO  <= m.m.Values;
  m.boundsNestingFromCalid(b, m.oHeap+m.ns);
}
