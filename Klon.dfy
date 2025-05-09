//future refactoring TODOs
// oHeap -> contest
// o -> pivot
// o -> ?? nuOwner
// shoiuld klon(c') functions become fgunctiosn on Klon?


predicate klonEQ(c' : Klon, c : Klon)
{
  && (c'.m == c.m)
  && (c'.o == c.o)
  && (c'.o_amfx  == c.o_amfx)
  && (c'.c_owner == c.c_owner)
  && (c'.c_amfx  == c.c_amfx)
  && (c'.oxtra   == c.oxtra)
  && (c'.cxtra   == c.cxtra)
  && (c'.oHeap == c.oHeap)
  && (c'.ns == c.ns)
}

predicate klonLEQ(c' : Klon, c : Klon)
{
  && (mapLEQ(c'.m, c.m))
  && (c'.o == c.o)
  && (c'.o_amfx  == c.o_amfx)
  && (c'.c_owner  == c.c_owner)
  && (c'.c_amfx  == c.c_amfx)
  && (c'.oxtra   == c.oxtra)
  && (c'.cxtra   == c.cxtra)
  && (c'.oHeap == c.oHeap)
  && (c'.ns <= c.ns)
}


function klonKV(c' : Klon, k : Object, v : Object) : (c : Klon)
//extends klon mapping with k:=v
//  requires klonVMapOK(c'.m)
  requires klonCanKV(c', k, v) //klonSatanKV(c', k, v)zz

  ensures  c == c'.(ns := c'.ns + nu(k,v)).(m:= VMapKV(c'.m,k,v))
  ensures  klonVMapOK(c.m)
  ensures  (forall x <- c'.m.Keys :: c.m[x] == c'.m[x])
  ensures  c.m[k] == v
  ensures  (forall x <- c.m.Keys :: c.m[x] ==
              if (x == k) then (v) else (c'.m[x]))

  ensures  klonLEQ(c',c)
  ensures  c.o == c'.o
  ensures  c.o_amfx  == c'.o_amfx
  ensures  c.c_owner == c'.c_owner
  ensures  c.c_amfx  == c'.c_amfx
  ensures  mapLEQ(c'.m,c.m)
  ensures  c.ns == c'.ns + nu(k,v)
  ensures  c.oHeap == c'.oHeap
  ensures  c.from(c')
  ensures  c.ns !! c'.ns


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

//grrr. should refactor this
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

//&& (v.AMFO >= v.AMFB >= k.AMFB)
  && (v.AMFX >= v.AMFB >= k.AMFB) //is this right?   really?


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

predicate klonVMapOK(m : vmap<Object,Object>, ks : set<Object> := m.Keys)
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
//klonca
// IDEALLY the "mapThru" features shouldn't be part of
// the invariuant itself (klonOK) NOR the extension test (klonCanKV)
// no the extension (klonKV)
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
  requires m0.readyAll()
//  requires m0.readyOK(k)
//  requires forall o <- m0.m.Keys :: m0.readyOK(o) //more or less m0.readyAll()
//  requires allMapOwnersThruKlownOK(m0)  //akq "allMapOwnersThruKlownOK"
  requires m0.readyAll()
  requires checkClownershipAllObjects(m0)
  requires klonAllOwnersAreCompatible(m0)
  requires m0.calid()
  requires MFUCKING: m0.calid()
  requires klonVMapOK(m0.m)
  requires klonCanKV(m0, k, v)

  requires k in m0.oHeap
  requires COK(k, m0.oHeap)
  requires (v==k) ==> (v in m0.oHeap)
  requires (v==k) ==> (COK(v,m0.oHeap))
  requires (v!=k) ==> (COK(v,m0.oHeap+m0.ns+{v}))
  requires (v!=k) ==> v in m1.ns
  requires (v!=k) ==> COK(v,m1.ns)

  requires k.Ready()
  requires m1 == klonKV(m0, k, v)
  requires mapGEQ(m1.m, m0.m)
  requires klonLEQ(m0, m1)

  requires (v==k) == (outside(k, m0.o))
  requires (v!=k) ==> (v.fields == map[]) //KJX FRI20DEC - new objects being added need to be empty?
  requires mappingOwnersThruKlownOK(k,m1) //THIS iS A BIT WEIRD as a "requires".. but
  requires forall o <- m0.m.Keys :: m0.readyOK(o)

  ensures klonVMapOK(m1.m)
  ensures m1.readyAll()
  ensures allMapOwnersThruKlownOK(m1)
  ensures checkClownershipAllObjects(m1)
  ensures m1.calid()
  {
    calidKV(m0,k,v,m1);

    //preconds KlonKVRestoresReadyAll
      assert klonCanKV(m0, k, v);
      assert m1 == klonKV(m0, k, v);
      assert m0.readyAll();
//      assert m0.readyOK(k);
      assert k.Ready();
      assert m0.ownersInKlown(k);
      assert m0.readyOK(k);

    KlonKVRestoresReadyAll(k,v,m0,m1);
    //end call
    klonAllRefsKVOK(k,v,m0,m1);

  }





//
//
// lemma {:verify false} OLDklonCalidKVCalid(m0 : Klon, k : Object, v : Object, m1 : Klon)
//   requires m0.readyAll()
//   requires forall o <- m0.m.Keys :: m0.readyOK(o)
//   requires allMapOwnersThruKlownOK(m0)  //akq "allMapOwnersThruKlownOK"
//   requires klonAllOwnersAreCompatible(m0)
//   requires m0.calid()
//   requires MFUCKING: m0.calid()
//   requires klonVMapOK(m0.m)
//   requires klonCanKV(m0, k, v)
//
//   requires k in m0.oHeap
//   requires COK(k, m0.oHeap)
//   requires (v==k) ==> (v in m0.oHeap)
//   requires (v==k) ==> (COK(v,m0.oHeap))
//   requires (v!=k) ==> (COK(v,m0.oHeap+m0.ns+{v}))
//   requires (v!=k) ==> v in m1.ns
//   requires (v!=k) ==> COK(v,m1.ns)
//
//   requires k.Ready()
//   requires m1 == klonKV(m0, k, v)
//   requires mapGEQ(m1.m, m0.m)
//   requires klonLEQ(m0, m1)
//
//   requires (v==k) == (outside(k, m0.o))
//   requires (v!=k) ==> (v.fields == map[]) //KJX FRI20DEC - new objects being added need to be empty?
//
//   requires mappingOwnersThruKlownOK(k,m1) //THIS iS A BIT WEIRD as a "requires".. but
//
//   requires forall o <- m0.m.Keys :: m0.readyOK(o)
//   ensures klonVMapOK(m1.m)
//   ensures m1.readyAll()
// //  ensures allMapOwnersThruKlownOK(m1)
// //   ensures m1.calid()
//   {
//   assert k !in m0.m.Keys;
//   assert v !in m0.m.Values;
//   assert k  in m0.oHeap;
//   assert m0.ownersInKlown(k);
//   assert klonCanKV(m0,k,v);
//   assert m1 == klonKV(m0,k,v);
//   assert m1.from(m0);
//   assert m0.readyAll();
//   assert m0.o_amfx <= m0.m.Keys ;
//   assert forall o <- m0.m.Keys :: m0.readyOK(o);
//   assert forall o <- m0.m.Keys :: m0.ownersInKlown(o);
//   assert allMapOwnersThruKlownOK(m0);
//   assert k.Ready();
//   assert m1.m.Keys >= k.bound;
//   assert m1.m.Keys >= k.ntrnl > k.owner >= k.bound;
//   assert m1.m.Keys >= k.AMFO  > k.AMFX  >= k.AMFB;
//   assert k.owner <= m1.m.Keys;
//   assert k.AMFO  <= m1.m.Keys;
//
//   assert mappingOwnersThruKlownOK(k,m1);
//
//
//   //  allMapOwnersThruKlownKV(m0,k,v,m1);
//
//
// assert m1.readyAll() by {
//   assert m0.readyAll();
//   assert m0.o_amfx <= m0.m.Keys;
//   assert klonLEQ(m0, m1);
//   assert m1.o_amfx <= m1.m.Keys;
//   assert m1.readyOK(k);
//
//   forall kk <- m1.m.Keys ensures m1.readyOK(kk) //by
//     {
//       if (kk == k)   {assert m1.readyOK(k);}
//         else {
//           assert allMapOwnersThruKlownOK(m0);
//           assert kk in m0.m.Keys;
//           mapThruKlownMapsOK3(kk, m0);
//           assert mappingOwnersThruKlownOK(kk,m0);
//           assert klonLEQ(m0, m1);
//           mapThruKlownMapsOK2(kk,m0,m1);
//           assert mappingOwnersThruKlownOK(kk,m1);
//
//           assert m1.readyOK(kk) by {
//             assert m0.readyAll();
//             assert kk in m0.m.Keys;
//             assert m0.readyOK(kk);
//             mapThruKlownMapsOK4(kk,m0);
//             assert kk.Ready();
//             assert kk in m1.m.Keys;
//             assert m1.ownersInKlown(kk);
//           }
//         } //end kk = k, i.e. kk in m0.m.Keys
//
//     } // end for
//   assert m1.readyAll();
//   } // end assert m1.readyAll(); //KJX !!!
//
//
//
// assert m1.calidObjects() by {
//   var c := m0;
//   var d := m1;
//
//   assert klonVMapOK(c.m);
//   assert klonCanKV(c, k, v);
//   assert d == klonKV(c, k, v);
//   assert c.calidObjects() || c.calid();
//   assert c.o in c.oHeap by {
//       assert m0.calid() by { reveal MFUCKING; }
//       reveal m0.calid();
//       assert m0.calidObjects(); reveal m0.calidObjects();
//       assert m0.o in m0.oHeap;
//       assert c.o in c.oHeap;
//       } //end   assert c.o in c.oHeap
//
// c.calidObjectsFromCalid();
//   assert c.m.Keys <= c.oHeap;
//
//   if (v==k) {
//      assert nu(k,v) == {};
//      assert c.ns + nu(k,v) == d.ns;
//      assert c.ns !! c.oHeap by { c.calidObjectsFromCalid();  assert c.ns !! c.oHeap; }
//      assert  (c.ns + nu(k,v)) !! c.oHeap;
//   } else {
//      assert v!=k;
//      assert k!=v;
//      assert NUK2(k!=v, v) == {v};
//      //   NUKV(k,v,{v});
//      assert nu(k,v) == {v};
//      assert c.ns + nu(k,v) == c.ns + {v} == d.ns;
//      assert v !in c.oHeap;
//
//      assert v in  d.ns;
//      assert v !in d.oHeap;
//      assert d.ns !! c.oHeap;
//      assert c.ns !! c.oHeap by { c.calidObjectsFromCalid();  assert c.ns !! c.oHeap; }
//
//      assert  (c.ns + nu(k,v)) !! c.oHeap;
//   }
//
//
//
//   assert  (c.ns + nu(k,v)) !! c.oHeap;
//   assert c.m.Values <= c.ns + c.oHeap by { c.calidObjectsFromCalid(); assert c.m.Values <= c.ns + c.oHeap; }
//   assert c.ns <= c.m.Values by {reveal MFUCKING; reveal m0.calid();  }
//   m1.KlonExtendsCalidObjects(m0, k, v, m1);
//   assert d.calidObjects();
// }
//  assert m1.calidObjects();
//
//     reveal m1.calidOK();
//     reveal m1.calidMap();
//     reveal m1.calidSheep();
//
//     assert m1.calidOK();
//     assert m1.calidMap();
//     assert m1.calidSheep();
//
//     assert m1.calid() by { reveal m1.calid(); }
//   }//emd KlonKCalidKVCalid

//

//
//     assert m1.calidObjects() by {
//       reveal Klon.calidObjects();
//       assert m0.calid() by { reveal MFUCKING; }
//       assert m0.calidObjects() by {
//           reveal m0.calid();
//       }
//       reveal Klon.calidObjects();
//       assert m1.o in m1.oHeap;
//       assert m1.m.Keys <= m1.oHeap;
//
//       assert m1.ns !! m1.oHeap by {
//       reveal Klon.calidObjects();
//
//       }
//
//       assert m1.m.Values <= m1.ns + m1.oHeap;
//       assert m1.ns <= m1.m.Values;
//       assert m1.calidObjects();
//     }

// lemma {:verify false} FUCKEDklonCalidKVCalid(m0 : Klon, k : Object, v : Object, m1 : Klon)
//   requires m0.readyAll()
//   requires allMapOwnersThruKlownOK(m0)  //akq "allMapOwnersThruKlownOK"
//   requires klonAllOwnersAreCompatible(m0)
//   requires m0.calid()
//   requires MFUCKING: m0.calid()
//   requires klonVMapOK(m0.m)
//   requires klonCanKV(m0, k, v)
//
//   requires k in m0.oHeap
//   requires COK(k, m0.oHeap)
//   requires (v==k) ==> v in m0.oHeap
//   requires (v==k) ==> (COK(v,m0.oHeap))
//   requires (v!=k) ==> (COK(v,m0.oHeap+m0.ns+{v}))
//
//   requires k.Ready()
//   requires m0.ownersInKlown(k)
//
//   requires m1 == klonKV(m0, k, v)
//   requires mapGEQ(m1.m, m0.m)
//   requires klonLEQ(m0, m1)
//
//   requires (v==k) == (outside(k, m0.o))
//
//   requires (v!=k) ==> (v.fields == map[]) //KJX FRI20DEC - new objects being added need to be empty?
//
//   ensures klonVMapOK(m1.m)
//   ensures m1.readyAll()
//   ensures allMapOwnersThruKlownOK(m1)
//   ensures m1.calid()
//   {
//         reveal m0.calid(), m0.calidObjects(), m0.calidOK(), m0.calidMap(), m0.calidSheep();
//         KlonKVVMapOK(m0, k, v, m1);
// IHasCalidMap(m0);
//
//
//   assert m1 == klonKV(m0, k, v);
//   assert (forall x <- m0.m.Keys :: (m1.m[x] == m0.m[x]));
//
//
//   //calidObiects
//         assert m0.ns !! m0.oHeap;
//         assert (v==k) ==> v in m0.oHeap;
//         assert m1.oHeap == m0.oHeap;
//         assert m1.ns == (m0.ns + nu(k,v));
//         assert m1.ns !! m0.oHeap;
//
//         assert
//             && (m1.o in m1.oHeap)
//             && (m1.m.Keys <= m1.oHeap)
//             && (m1.ns !! m1.oHeap)
//             && (m1.m.Values <= m1.ns + m1.oHeap)
//             && (m1.ns <= m1.m.Values)
//             ;
//         assert m1.calidObjects();
//
//
// //calidOK
//         assert
//             && (m1.o in m1.oHeap)
//             && (m1.m.Keys <= m1.oHeap)
//             && (m1.m.Values <= m1.oHeap+m1.ns)
//             && COK(m1.o, m1.oHeap)
//             && CallOK(m1.oHeap);
//
//       CallOKfromCOK(k,m0.oHeap);
//       CallOKWiderFocus(m0.m.Keys, {k}, m0.oHeap);
//       assert CallOK(m1.m.Keys, m1.oHeap);
//
//
//   assert (v !in m0.ns);
//   assert (v==k) ==> (COK(v,m0.oHeap));
//   assert (v!=k) ==> (COK(v,m0.oHeap+m0.ns+{v}));
//
//       assert CallOK(m0.m.Values, m0.oHeap+m0.ns);
//
// if (v == k)  {
//    assert v in m0.oHeap;
//    assert m1 == klonKV(m0,k,v);
//    assert m1.oHeap == m0.oHeap;
//    assert m1.ns == m0.ns;
//    assert v in m1.oHeap;
//
//    assert CallOK(m0.ns, m0.oHeap+m0.ns);
//    assert CallOK(m1.ns, m1.oHeap+m1.ns);   //cos ==
//
//    assert (COK(v,m1.oHeap));
//    CallOKfromCOK(v,m1.oHeap);
//    assert CallOK({v},m1.oHeap);
//    CallOKWiderContext({v},m1.oHeap,m1.ns);
//    assert CallOK({v},m1.oHeap+m1.ns);
//
//    assert CallOK(m0.m.Values, m0.oHeap+m0.ns);
//    assert CallOK(m0.m.Values, m1.oHeap+m1.ns);   //cos ==
//    CallOKWiderFocus(m0.m.Values,{v},m1.oHeap+m1.ns);
//    assert CallOK(m0.m.Values+{v}, m1.oHeap+m1.ns);
//    assert m1.m.Values == m0.m.Values + {v};
//    assert CallOK(m1.m.Values, m1.oHeap+m1.ns);
//
//
//
//
//   assert klonAllOwnersAreCompatible(m0);
//   assert k !in m0.m.Keys;
//   assert k  in m1.m.Keys;
//   klonSameOwnersAreCompatible(k,v,m1);
//
// assert mapGEQ(m1.m, m0.m);
// assert COK(k, m0.oHeap);
//
// assert klonOwnersAreCompatible(k, v, m0);
//
//
//
//   klonOwnersAreCompatibleKV(k,v,m0,m1);
//   assert klonOwnersAreCompatible(k,v,m1);
//   forall  o <- m1.m.Keys
//     ensures
//      klonOwnersAreCompatible(o,m1.m[o],m1)
//     {
//       if (o == k) {
//           //klonOwnersAreCompatibleKV(k,v,m0,m1);
//           assert klonOwnersAreCompatible(o,m1.m[o],m1);
//       } else {
//           assert klonAllOwnersAreCompatible(m0);
//           assert o in m0.m.Keys;
//           assert klonOwnersAreCompatible(o,m0.m[o],m0);
//           assert m0.m[o] == m1.m[o];
//           assert klonOwnersAreCompatible(o,m1.m[o],m1);
//       }
//     }
//
//   assert klonAllOwnersAreCompatible(m1);
//   assert m0.readyAll();
//   assert allMapOwnersThruKlownOK(m0);
//
//
// assert klonLEQ(m0, m1);
//
// assert m1.readyAll() by {
//   assert m0.readyAll();
//   assert m0.o_amfx <= m0.m.Keys;
//   assert klonLEQ(m0, m1);
//   assert m1.o_amfx <= m1.m.Keys;
//   assert m1.readyOK(k);
//
//   forall kk <- m1.m.Keys ensures m1.readyOK(kk) //by
//     {
//       if (kk == k)   {assert m1.readyOK(k);}
//         else {
//           assert kk in m0.m.Keys;
//           assert m0.readyOK(kk);
//
//           }
//     }
//
//   assert m1.readyAll();
//   }
//   //  assert allMapOwnersThruKlownOK(m1);
//
//
//   assert klonVMapOK(m1.m);
//
//   forall kk <- m1.m.Keys ensures mappingOwnersThruKlownOK(kk,m1) //by
//     {
//       if (kk == k)   {assuage mappingOwnersThruKlownOK(k,m0);}
//         else {
//           assert mappingOwnersThruKlownOK(k,m0) by
//            {
//               assert allMapOwnersThruKlownOK(m0);
//               assert kk in m0.m.Keys;
//               assert mappingOwnersThruKlownOK(k,m0);
//          }
//           mapThruKlownMapsOK2(k,m0,m1);
//           assert mappingOwnersThruKlownOK(k,m1);
//           }
//     }
//   assert allMapOwnersThruKlownOK(m1);
//
//   assert allMapOwnersThruKlownOK(m1);
//
//    assert m1.calid();
//
//   assert m1.readyAll();
//   return;
//
//
// } else {
//    assert v != k;
//
//   assuage klonVMapOK(m1.m) && m1.readyAll() && allMapOwnersThruKlownOK(m1) && m1.calid();
//   return;
//
//    assert m1 == klonKV(m0,k,v);
//    assert m1.oHeap == m0.oHeap;
//    assert m1.ns == m0.ns+{v};
//    assert v in m1.ns;
//
//    assert (COK(v, m0.oHeap+m0.ns+{v}));
//    assert m0.oHeap+m0.ns+{v}   ==  m0.oHeap+(m0.ns+{v});
//    assert m0.oHeap+(m0.ns+{v}) ==  m1.oHeap+m1.ns;
//    assert COK(v, m1.oHeap+m1.ns);
//    CallOKfromCOK(v,m1.oHeap+m1.ns);
//    assert CallOK({v},m1.oHeap+m1.ns);
//
//    assert CallOK(m0.ns, m0.oHeap+m0.ns);
//    CallOKWiderContext(m0.ns, m0.oHeap+m0.ns, {v});
//    assert CallOK(m0.ns, m0.oHeap+m0.ns+{v});
//    assert m0.oHeap+m0.ns+{v}   ==  m0.oHeap+(m0.ns+{v});
//    assert m0.oHeap+(m0.ns+{v}) ==  m1.oHeap+m1.ns;
//    assert CallOK(m0.ns, m1.oHeap+m1.ns);
//    CallOKWiderFocus(m0.ns,{v},m1.oHeap+m1.ns);
//    assert CallOK(m0.ns+{v}, m1.oHeap+m1.ns);
//    assert CallOK(m1.ns, m1.oHeap+m1.ns);
//
//
//    assert CallOK(m0.m.Values, m0.oHeap+m0.ns);
//    assert CallOK(m0.m.Values, m1.oHeap+m0.ns);  //not the same.
//    CallOKWiderContext(m0.m.Values, m1.oHeap+m0.ns, {v});
//    assert CallOK(m0.m.Values, m1.oHeap+m0.ns+{v});
//    assert CallOK(m0.m.Values, m1.oHeap+(m0.ns+{v}));
//    assert m0.ns+{v} == m1.ns;
//    assert CallOK(m0.m.Values, m1.oHeap+m1.ns);
//
//    CallOKWiderFocus(m0.m.Values,{v},m1.oHeap+m1.ns);
//    assert CallOK(m0.m.Values+{v}, m1.oHeap+m1.ns);
//    assert m1.m.Values == m0.m.Values + {v};
//    assert CallOK(m1.m.Values, m1.oHeap+m1.ns);
//
//
// assert v.fields == map[];
//     assert klonAllOwnersAreCompatible(m0);
//     assert klonOwnersAreCompatible(k,v,m1);
//
// assert forall o <- m0.m.Keys :: klonOwnersAreCompatible(o,m0.m[o],m0);
//   assert k !in m0.m.Keys;
// assert forall o <- m0.m.Keys :: m1.m[o] == m0.m[o];
// assert m0.m.Keys == m1.m.Keys - {k};
// assert forall o <- m0.m.Keys :: klonOwnersAreCompatible(o,m1.m[o],m0);
//
// assert forall o <-(m1.m.Keys - {k}):: klonOwnersAreCompatible(o,m1.m[o],m0);
//
//
// //TODO  -  NEED EXISTENTIONALITY for both k==v and k!=v
// //can't do it this way cos of CALIDituty
//
//     assert m1.m == m0.m[k:=v];
//
//     //assert klonAllOwnersAreCompatible(m1);
//
//     assert m0.readyAll();
//     assert allMapOwnersThruKlownOK(m0);
//
// //assert wexford(m0);
// //wexfordKV(k,v,m0,m1);
// //assert wexford(m1);
//
//
//
//     klonAllRefsKVOK(k,v,m0,m1);
//
//     assert m1.readyAll();
//     assert allMapOwnersThruKlownOK(m1);
//
//
//    }//end case v != k
//
//       assert CallOK(m1.m.Values, m1.oHeap+m1.ns);
//       assert CallOK(m1.ns, m1.oHeap+m1.ns);
//
//         assert m1.calidOK();
//
// //calidMap
// assert
//     && AllMapEntriesAreUnique(m1.m)
//     && klonVMapOK(m1.m) // potentiall should expand this out?
//     // && (forall x <- m1.m.Keys, oo <- x.AMFO :: m1.m[oo] in m1.m[x].AMFO)
//     // && (forall x <- m1.m.Keys, oo <- x.AMFB :: m1.m[oo] in m1.m[x].AMFB)
// ;
//
// assert (forall x <- m0.m.Keys :: (not(inside(x,m0.o)) ==> (m0.m[x] == x)));
// assert m1.o == m0.o;
// assert (forall x <- m0.m.Keys :: (m1.m[x] == m0.m[x]));
// assert (forall x <- m0.m.Keys :: (not(inside(x,m1.o)) ==> (m1.m[x] == x)));
// assert m1.m[k] == v;
// assert m1.m.Keys == m0.m.Keys + {k};
// assert m1.o == m0.o;
// assert (forall x <- m1.m.Keys :: m1.m[x] == (
//          if (x in m0.m.Keys)
//            then (assert (m1.m[x] == m0.m[x]); (m0.m[x]))
//            else (assert x == k; assert (outside(x,m0.o)) ==> (m1.m[x] == x == k == v); (m1.m[x]))));
//
// assert forall x <- m1.m.Keys :: (not(inside(x,m1.o)) ==> (m1.m[x] == x));
//
// //assert forall x <- m0.m.Keys, oo <- x.owner :: m0.m[oo] in m0.m[x].owner;
// assert m1.m[k] == v;
// // assert forall oo <- k.owner :: m1.m[oo] in v.owner;
// // assert forall x <- m1.m.Keys, oo <- x.owner :: m1.m[oo] in m1.m[x].owner;
// // assert forall x <- m1.m.Keys, oo <- x.AMFO :: m1.m[oo] in m1.m[x].AMFO;
// IHasCalidMap(m0);
// assert (forall x <- m0.m.Keys ::
//         && m0.boundsNestingOK(x, m0.oHeap)
//         && m0.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns)
//         && m0.fieldMappingsOK(x, m0.m[x], m0.m.Keys));
//
// assert
//         && m0.boundsNestingOK(k, m0.oHeap)
//         && m0.boundsNestingOK(v, m0.oHeap+m0.ns+{v})
//         && m0.fieldMappingsOK(k, v, m0.m.Keys+{k});
//
// assert m1.m[k]        == v;
// assert m1.m.Keys      == m0.m.Keys + {k};
// assert m1.m.Values    == m0.m.Values+{v};
// assert m1.oHeap       == m0.oHeap;
// assert m1.oHeap+m1.ns == m0.oHeap+m0.ns+{v};
// assert m1.o           == m0.o;
// assert m1.m[k] == v;
//
// assert
//         && m1.boundsNestingOK(k, m1.oHeap)
//         && m1.boundsNestingOK(m1.m[k], m1.oHeap+m1.ns)
//         && m1.fieldMappingsOK(k, m1.m[k], m1.m.Keys);
//
//   assert m1.calidOK();
//   assert m1.calidObjects();
//   assert AllMapEntriesAreUnique(m1.m);
//   assert klonVMapOK(m1.m);
//   assert (forall x <- m1.m.Keys :: (not(inside(x,m1.o)) ==> (m1.m[x] == x)));
//
// assert (forall x <- m0.m.Keys ::
//         && m1.boundsNestingOK(x, m0.oHeap)
//         && m1.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns)
//         && m1.fieldMappingsOK(x, m0.m[x], m0.m.Keys));
//
//   assert (forall x <- m0.m.Keys :: m1.m[x] == m0.m[x]);
//
// //  m1.boundsNestingWiderContext(v,m0.oHeap+m0.ns, m0.oHeap+m0.ns+{v});
//   assert (forall x <- m0.m.Keys :: (m0.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns)));
//   assert (forall x <- m0.m.Keys ::
//     && (m0.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns))
//     && (m1.m[x] == m0.m[x])
//     && (m0.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns)));
//
//   assert 7: (forall x <- m0.m.Keys :: (m1.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns)));
//
//   assert 75: (forall x <- m0.m.Keys ::
//      && (m1.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns))
//      && COK(m1.m[x], m0.oHeap+m0.ns)
//     // && COK(m1.m[x], m0.oHeap+m0.ns+{v})
//     // && COK(m1.m[x], m1.oHeap+m1.ns+{v})
//   );
//
// forall x | x in m0.m.Keys ensures (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns)) {
//       assert m1.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns);
//       assert  COK(m1.m[x], m0.oHeap+m0.ns);
//       COKWiderContext2(m1.m[x],m0.oHeap+m0.ns,m0.oHeap+m0.ns+{v});
//       assert  COK(m1.m[x], m0.oHeap+m0.ns+{v});
//       assert m1.boundsNestingOK(m1.m[x], m0.oHeap+m0.ns+{v});
//       assert m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns);
// }
//
//
//
//   assert 8: (forall x <- m0.m.Keys :: (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns)));
//
// //   assert (forall x <- m0.m.Keys :: (m0.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns)));
// //   assert (forall x <- m0.m.Keys :: (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns)));
// // //
// //
// //   assert (forall x <- m0.m.Keys :: m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));
// //
// //   assert (forall x <- m0.m.Keys :: m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));//FUCKED
// //   assert (forall x <- (m0.m.Keys+{k}) :: m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));
// //   assert (forall x <- m1.m.Keys :: m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));
//
//
//
//     IHasCalidMap(m1);
//     assert m1.calidMap();  //FUCKA
//
// //calidSheepKV
//     reveal m0.AreWeNotMen();
//     reveal UniqueMapEntry();
// assert
//     && (forall x <- m0.m.Keys :: m0.AreWeNotMen(x, m0))
//     && (forall x <- m0.m.Keys :: m0.m[x].fieldModes == m1.m[x].fieldModes)
//     && AllMapEntriesAreUnique(m0.m);
// FORALLAWNMFUCKED(m0,m1);
// assert
//     && (forall x <- m0.m.Keys :: m1.AreWeNotMen(x, m1))
//     && (forall x <- m1.m.Keys :: x.fieldModes ==
//           if (x in m0.m.Keys)
//               then (m1.m[x].fieldModes)
//               else (assert (x == k) && (m1.m[x] == v) && (k.fieldModes == v.fieldModes); v.fieldModes)
//        )
//     && AllMapEntriesAreUnique(m1.m)
//     ;
//
// IHasCalidSheep(m1);
//         assert m1.calidSheep();
//
//         assert m1.from(m0);
//         assert m1.calid();
//   }
//

datatype Klon = Klon
(
  m : vmap<Object,Object>, // maps from Original to Clone (or non-clone)
//  m.Keys : set<Object>, //m.Keys - set, keys of the mapping   (must be m.Keys, subset of oHeap)
//  m.Values : set<Object>, //m.Values - set, values or the mapping (must be m.Values, subset of oHeap + ns)
  o : Object,  //o -  within which the clone is being performaed, in oHeap  // "pivot"
      // or rather is the fucking OBJECT to be CLONED???
  //    p : Object,  // Owner of the new (target) clone.  needs to be inside the source object's movement

  o_amfx  : Owner,             //was o. so the AMFO of o
  c_owner : Owner,             //prooposed owner of c
  c_amfx  : Owner,             //amfx of clone... - can't have AMFO cos c likely hasn't been created yet.

  oxtra   : Owner,
  cxtra   : Owner,

//wboops need the  NEW BOUND too HUH?

  oHeap : set<Object>,  //oHeap - original (sub)heap contianing the object being cloned and all owners and parts
  ns : set<Object>      //ns - new objects  (must be !! oHeap,   m.Values <= oHeap + ns
  )

{



//
// predicate klonLEQ(c' : Klon, c : Klon)
// {
//   && (mapLEQ(c'.m, c.m))
//   && (c'.o == c.o)
//   && (c'.o_amfx  == c.o_amfx)
//   && (c'.c_owner  == c.c_owner)
//   && (c'.c_amfx  == c.c_amfx)
//   && (c'.oHeap == c.oHeap)
//   && (c'.ns <= c.ns)
// }
//



  predicate from(prev : Klon)
    //current Klon has come from prev Klon
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    reads prev.oHeap`fields, prev.oHeap`fieldModes
    reads prev.ns`fields, prev.ns`fieldModes
    //     requires calid()
    //     requires prev.calid()
  {
    reveal calid(), calidObjects(), calidOK(), calidMap(), calidSheep();
    && mapGEQ(m, prev.m)
    && o       == prev.o
    && o_amfx  == prev.o_amfx
    && c_owner == prev.c_owner
    && c_amfx  == prev.c_amfx
    && oHeap   == prev.oHeap
    && ns      >= prev.ns

  && (oxtra   == prev.oxtra)
  && (cxtra   == prev.cxtra)

    //&& calid()         //should these be requirements?
    //&& prev.calid()   //currently NO because??? the underlyign thing will require calid and reutnr calid
  }

  lemma FROMFROM(prev : Klon, midd : Klon, succ : Klon)
    requires midd.from(prev)
    requires succ.from(midd)
    ensures  succ.from(prev)
    {}

  twostate predicate allUnchangedExcept(except : set<Object> := {})
    reads m.Values, m.Keys, o, oHeap
  {
    &&  unchanged(m.Values - except)
    &&  unchanged(m.Keys - except)
    &&  unchanged({o} - except)
    &&  unchanged(oHeap - except)
  }


  predicate readyOK(o : Object)
     //o is Ready, in m.Keys, and all owners are in m.Keys...
  {
    && o.Ready()
    && (o in m.Keys)    //same as objectsInKlown(o)
    && (ownersInKlown(o))

//     && (o.AMFB <= m.Keys)
//     && (o.AMFX <= m.Keys)
//     && (o.AMFO <= m.Keys)
//
//     && (o.bound <= m.Keys)
//     && (o.owner <= m.Keys)
//     && (o.ntrnl <= m.Keys)
  }

lemma ReadyOKDUCKED(o : Object)
  requires readyOK(o)
  ensures  o.Ready()
  {}


  predicate objectInKlown(o : Object)
   //o and all its owners etc are the Klown m
   //(doesn't extend to fields)
   //note no o.Ready() or such thing...
   //probably be a good idea
{
    && (o.AMFB <= m.Keys)
    && (o.AMFX <= m.Keys)
    && (o.AMFO <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA

    && (o.bound <= m.Keys)
    && (o.owner <= m.Keys)
    && (o.ntrnl <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA
}


  predicate alternateObjectInKlown(o : Object) : (rv : bool)
   //o and all its owners etc are the Klown m
   //(doesn't extend to fields)
   //note no o.Ready() or such thing...
   //probably be a good idea
    requires o.Ready()

    ensures o.AMFO  > o.AMFX  >= o.AMFB
    ensures o.ntrnl > o.owner >= o.bound
    ensures rv ==> (o in m.Keys)
    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.AMFO <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
    ensures rv ==> (o.ntrnl <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA
{
    assert o.AMFO  > o.AMFX  >= o.AMFB;
    assert o.ntrnl > o.owner >= o.bound;

    (o.AMFO <= m.Keys)
}

  predicate ownersInKlown(o : Object)
{
    && (o.AMFB <= m.Keys)
    && (o.AMFX <= m.Keys)
//    && (o.AMFO <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA

    && (o.bound <= m.Keys)
    && (o.owner <= m.Keys)
//    && (o.ntrnl <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA
}

lemma KLOWNAMFO(o : Object)
  requires o.Ready()
  requires o.AMFO <= m.Keys
  requires o_amfx <= m.Keys

  ensures  objectInKlown(o)
  ensures  ownersInKlown(o)
  ensures  canMapOwnersThruKlown(o, this)
  {
    reveal o.Ready();
  }





lemma KLOWNKLUB(o : Object)
  requires objectInKlown(o)
  ensures  ownersInKlown(o)
  {}


lemma KLUBKLOWN(o : Object)
  requires readyOK(o)
  ensures  ownersInKlown(o)
  {}


  // lemma AllMys(o : Object)
  //   requires readyOK(o)
  //   ensures  forall oo <- o.AMFX :: readyOK(oo)
  //   {}


   predicate readyAll()
   //should be called "klownMapOK"e
     // all keys are readyOK
     //should be called calldReady????
     //or calidKlown, or klownMapOK...
   {
      && (o_amfx <= m.Keys)
      && (oxtra == mapThruKlon(o_amfx, this) - c_amfx)
      && (cxtra == c_amfx - mapThruKlon(o_amfx, this))

      && (forall k <- m.Keys :: readyOK(k))
   }

//
// predicate klownMapOK()
// {
//   && (o_amfx <= m.Keys)
//   && (cxtra == c_amfx - mapThruKlon(o_amfx, this))
//   && (oxtra == mapThruKlon(o_amfx, this) - c_amfx)
// }



///////////////////////////////////////////////////////////////////////////////////
// OLDER functions & SHIT on KLONs

  opaque function {:verify false} XXXat(k : Object) : (v : Object)
    //return value corresponding to key k
    //k must be in the map
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes

    //requires reveal calid(); reveal calidObjects();  m.Keys == m.Keys
    //requires k in m.Keys
    ensures  k in m.Keys //to guard the next one
    ensures  v == m[k]
  {  at(k) }


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



  opaque function {:verify false} XXXputInside(k : Object, v : Object) : (r : Klon)

    ensures  klonEQ(r,klonKV(this,k,v))
    ensures  klonLEQ(this, r)
    ensures  klonVMapOK(r.m)
    ensures  klonVMapOK(m)
    //ensures  r == Klon(VMapKV(m,k,v), o, oHeap, ns+{v})

    ensures  r.ns == ns+nu(k,v)
    ensures  v in r.ns
    ensures  k in r.m.Keys && r.m[k] == v
////    ensures  COK(v, r.oHeap+r.ns)
    ensures  k in r.m.Keys
    ensures  v in r.m.Values
    ensures  r.m.Values == m.Values + {v}
    ensures  r.m == m[k:=v]
    ensures  mapLEQ(m, r.m)
////    ensures  r.calid()
    ensures  r.from(this)
    ensures  AllMapEntriesAreUnique(this.m)
{
putin(k,v)
}


  opaque function putInside(k : Object, v : Object) : (r : Klon)
    reads oHeap`fields, oHeap`fieldModes
    reads k`fields, k`fieldModes
    reads v`fields, v`fieldModes
    reads ns`fields, ns`fieldModes
    reads m.Values`fieldModes
    reads m.Keys`fieldModes

    requires canVMapKV(m,k,v)
    requires calid()


////////////////
//// List from oldPutInside
///////////////

    requires calid()
    requires readyAll()
    requires allMapOwnersThruKlownOK(this) //lemma should be able to derive from calid()
    requires klonVMapOK(m) //lemma can derive from calid()

    requires canVMapKV(m,k,v)
    requires klonCanKV(this,k,v)
    requires AreWeNotMen(k, klonKV(this,k,v))
    requires (k.owner <= m.Keys) && (mapThruKlon(k.owner, this) == v.owner)

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
///////////////


    ensures  klonEQ(r,klonKV(this,k,v))
    ensures  klonLEQ(this, r)
    ensures  klonVMapOK(r.m)
    ensures  klonVMapOK(m)
    //ensures  r == Klon(VMapKV(m,k,v), o, oHeap, ns+{v})

    ensures  r.ns == ns+nu(k,v)
    ensures  v in r.ns
    ensures  k in r.m.Keys && r.m[k] == v
////    ensures  COK(v, r.oHeap+r.ns)
    ensures  k in r.m.Keys
    ensures  v in r.m.Values
    ensures  r.m.Values == m.Values + {v}
    ensures  r.m == m[k:=v]
    ensures  mapLEQ(m, r.m)
////    ensures  r.calid()
    ensures  r.from(this)
    ensures  AllMapEntriesAreUnique(this.m)


     { var rv := putin(k,v);
       assert klonLEQ(this, rv);
       rv
      }


  opaque function {:verify false} OLDputInside(k : Object, v : Object) : (r : Klon)
    //put k -> v into map, k inside o
    reads oHeap`fields, oHeap`fieldModes
    reads k`fields, k`fieldModes
    reads v`fields, v`fieldModes
    reads ns`fields, ns`fieldModes
    reads m.Values`fieldModes
    reads m.Keys`fieldModes

    requires calid()
    requires readyAll()
    requires allMapOwnersThruKlownOK(this) //lemma should be able to derive from calid()
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
var OLDrv := Klon(VMapKV(m,k,v), o, o_amfx, c_owner, c_amfx, oxtra, cxtra, oHeap, ns+nu(k,v));

var rv := this.(m := VMapKV(m,k,v), ns := ns+nu(k,v));

assert rv == OLDrv;

//////////////////////////////////////////////////////////////////////////////////////
// unpkacing KlonKV
//////////////////////////////////////////////////////////////////////////////////////

    assert  klonVMapOK(this.m);

      var cdouble := this.(m:= VMapKV(this.m,k,v));
      var nsv := (cdouble.ns + nu(k,v));
      var r   := cdouble.(ns:= nsv); (

      assert (forall k <-  this.m.Keys :: k.AMFO <= this.m.Keys);

      assert k.AMFO <= this.m.Keys + {k};

      assert  klonVMapOK(r.m);

      assert klonEQ(rv,r);

      assert   rv == r;

//////////////////////////////////////////////////////////////////////////////////////

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
            AddToDisjointSet(v,ns,oHeap);


        // assuage {v} !! oHeap;   //why do we need this given the above? - answer: to speed veriication?
        // assert (ns + {v}) !! oHeap;
        // assert rv.oHeap == oHeap;
        // assert (ns + {v}) !! rv.oHeap;
        // assert rv.ns == ns+{v};
        // assert rv.ns !! rv.oHeap;
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

assert readyAll();
assert allMapOwnersThruKlownOK(this);
assert calid();
assert klonVMapOK(m);
assert klonCanKV(this, k, v);

assert k in oHeap;
assert COK(k, oHeap);
assert COK(v,oHeap+ns+{v});


// klonCalidKVCalid(this, k, v, rv);

  assert klonVMapOK(rv.m);
  assert rv.readyAll();
  // assuage allMapOwnersThruKlownOK(rv);
  // assuage rv.calid();


  //  IHasCalidMap(rv);
    assert  rv.calidMap() by { reveal calid(); }

    // assert rv.calidMap() by {                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       bb
    //     reveal rv.calidObjects(); assert rv.calidObjects();bbbbbbbbbbbbbbbbbb
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
    )} //END putInside

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

//do I need this lot or just fold in and need just c.calid*()
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
      assert {:contradiction} c.calid();
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
    requires readyAll()
    requires allMapOwnersThruKlownOK(this)

    requires canVMapKV(m,k,k)
    requires klonCanKV(this,k,k)
    requires AreWeNotMen(k, klonKV(this,k,k))

    requires ownersInKlown(k)

    requires k  in oHeap
    requires k !in m.Keys
    requires k !in m.Values
    requires COK(k, oHeap)
    requires m.Keys <= oHeap
    requires k.allExternalOwners() <= m.Keys
  //  requires ownersInKlown(k)  ///I think this imples the above?


    // requires (k.owner <= m.Keys) && (mapThruKlon(k.owner, this) == k.owner)  //OK right but why require it?
    // requires mapThruKlonKV(k.AMFO, this, k, k) == k.AMFO   //OK right but why require it?

    requires outside(k, o)
       //see commetns above about "mapThruKlon(k.owner, this) == k.owner"

    ///////////////////////////////  WHOOP WHOOP DA SOUND OF DA POLICE
    requires canMapOwnersThruKlown(k, klonKV(this,k,k))
    requires canKlown(this, k, k,  klonKV(this,k,k))
    ///////////////////////////////  WHOOP WHOOP DA SOUND DAT I MISS

    ensures r == klonKV(this,k,k)
    ensures  klonVMapOK(r.m)
    ensures  klonVMapOK(m)

    ensures r.calid()
    ensures r.from(this)
{
    var r := klonKV(this,k,k);
    calidKV(this,k,k,r);
    r
}


  opaque function {:verify false} XXXputOutside(k : Object) : (r : Klon)
    //put k -> k into map, k oustide o
    reads oHeap`fields, oHeap`fieldModes
    reads k`fields, k`fieldModes
    reads ns`fields, ns`fieldModes
    reads o`fields, o`fieldModes
    reads m.Values`fieldModes
    reads m.Keys

    ensures r == klonKV(this,k,k)
    ensures klonVMapOK(r.m)
    ensures klonVMapOK(m)
    ensures r.calid()
    ensures r.from(this)
{
  putOutside(k)
}

  opaque function  {:verify false}  OLDputOutside(k : Object) : (r : Klon)
    //put k -> k into map, k oustide o
    reads oHeap`fields, oHeap`fieldModes
    reads k`fields, k`fieldModes
    reads ns`fields, ns`fieldModes
    reads o`fields, o`fieldModes
    reads m.Values`fieldModes
    reads m.Keys

    requires calid()
    requires klonVMapOK(m) //lemma can derive from calid()
    requires readyAll()
    requires allMapOwnersThruKlownOK(this)

    requires canVMapKV(m,k,k)
    requires klonCanKV(this,k,k)
    requires AreWeNotMen(k, klonKV(this,k,k))

    requires ownersInKlown(k)

    requires k  in oHeap
    requires k !in m.Keys
    requires k !in m.Values
    requires COK(k, oHeap)
    requires m.Keys <= oHeap
    requires k.allExternalOwners() <= m.Keys
  //  requires ownersInKlown(k)  ///I think this imples the above?


    // requires (k.owner <= m.Keys) && (mapThruKlon(k.owner, this) == k.owner)  //OK right but why require it?
    // requires mapThruKlonKV(k.AMFO, this, k, k) == k.AMFO   //OK right but why require it?

    requires outside(k, o)
       //see commetns above about "mapThruKlon(k.owner, this) == k.owner"

    ensures r == klonKV(this,k,k)
    ensures  klonVMapOK(r.m)
    ensures  klonVMapOK(m)

    ensures r.calid()
    ensures r.from(this)

{
    var r := klonKV(this,k,k); (
    reveal calid();
    assert calid();
    assert calidObjects();
    reveal calidObjects();
    reveal calidOK();
    assert calidOK();
    reveal calidMap();
    assert calidMap();
    reveal calidSheep();
    assert calidSheep();

    assert BAA:  calidSheep();


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

    assert ownersInKlown(k);
        //EEEEVVVIIOILLLL


klonCalidKVCalid(this, k, k, r);
    IHasCalidOK(r);
    IHasCalidMap(r);

    assert klonVMapOK(this.m);
    assert klonCanKV(this, k, k);
    assert r == klonKV(this, k, k);

    reveal calidSheep();
    assert calidSheep() by { reveal BAA; }
    reveal AreWeNotMen();
    assert forall x <- this.m.Keys :: AreWeNotMen(x, r);
    assert AreWeNotMen(k,r);
    KlonExtendsDEVO(this, k, k, r);

    IHasCalidSheep(r);
    IHasCalid(r);

    r
  )}


















































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




  opaque predicate AreWeNotMen(x : Object,  m0 : Klon)  //hmmm wgt etc?
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    requires x in m0.m.Keys
  {
    && (   (inside(x,m0.o)) ==> (m0.m[x] in m0.ns))
    && (not(inside(x,m0.o)) ==> (m0.m[x] == x))
    && (   (inside(x,m0.o)) ==> (UniqueMapEntry(m0.m,x)))
    && (not(inside(x,m0.o)) ==> (UniqueMapEntry(m0.m,x)))
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
    //if x is outsite rv.o"  (why RV??)
    //ad x isn't in m.m.Keys
    //then it's not in values either.
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

  predicate superCalid() : (r : bool)
    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
{
    && objectInKlown(o)
    && calid()
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
    requires calidObjects() && calidOK()

    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    reads m.Keys`fields,     m.Keys`fieldModes
    reads m.Values`fields,   m.Values`fieldModes
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

  //  && allMapOwnersThruKlownOK(this)

    && (forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x)))
    // && (forall x <- m.Keys, oo <- x.owner :: m[oo] in m[x].owner) //KJXOWNERS
    // && (forall x <- m.Keys, oo <- x.bound :: m[oo] in m[x].bound) //KJXOWNERS
    // && (forall x <- m.Keys, oo <- x.AMFO  :: m[oo] in m[x].AMFO)
    // && (forall x <- m.Keys, oo <- x.AMFB  :: m[oo] in m[x].AMFB)
  }

  opaque predicate  calidSheep2()
    requires calidObjects() && calidOK() && calidMap()

    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    reads m.Keys`fields,     m.Keys`fieldModes
    reads m.Values`fields,   m.Values`fieldModes
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
    requires calidObjects() && calidOK()// && calidMap()

    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    reads m.Keys`fields,     m.Keys`fieldModes
    reads m.Values`fields,   m.Values`fieldModes
  {
    reveal calidObjects();  assert calidObjects();
    reveal calidOK();       assert calidOK();
    //reveal calidMap();    assert calidMap();

    reveal AreWeNotMen();
    //reveal UniqueMapEntry();

    && (forall x <- m.Keys :: AreWeNotMen(x, this))
    && (forall x <- m.Keys :: x.fieldModes == m[x].fieldModes)
    && AllMapEntriesAreUnique(m)
  }



  opaque predicate calidSheep3()
    requires calidObjects() && calidOK() && calidMap()

    reads oHeap`fields, oHeap`fieldModes
    reads ns`fields, ns`fieldModes
    reads m.Keys`fields,     m.Keys`fieldModes
    reads m.Values`fields,   m.Values`fieldModes
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

    assert forall x <- m.Keys :: x.fieldModes == m[x].fieldModes
      by { reveal calidSheep2(); assert calidSheep2(); }

  }





lemma calidObjectsFromCalid()
  //unpacks calidObjects :-)
  requires calid()
  ensures o in oHeap
  ensures m.Keys <= oHeap
  ensures ns !! oHeap
  ensures m.Values <= ns + oHeap
  ensures ns <= m.Values
{
  reveal calid();
  reveal calidObjects();
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

lemma calidMapFromCalid()
  requires calid()
  ensures  AllMapEntriesAreUnique(m)
  ensures  klonVMapOK(m)
  ensures  (forall x <- m.Keys ::
        && boundsNestingOK(x, oHeap)
        && boundsNestingOK(m[x], oHeap+ns)
        && fieldMappingsOK(x, m[x], m.Keys))
  ensures  klonAllOwnersAreCompatible(this)
  ensures  (forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x)))
{
  reveal calid();
  reveal calidObjects();  assert calidObjects();
  reveal calidOK();       assert calidOK();
  reveal calidMap();      assert calidMap();
  reveal AreWeNotMen();


}

lemma calidSheepFromCalid()
  requires calid()
  ensures (forall x <- m.Keys :: AreWeNotMen(x, this))
  ensures (forall x <- m.Keys :: x.fieldModes == m[x].fieldModes)
  ensures AllMapEntriesAreUnique(m)
  {
  reveal calid();
  reveal calidObjects();  assert calidObjects();
  reveal calidOK();       assert calidOK();
  reveal calidSheep();    assert calidSheep();
  reveal CallOK();
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

//should be renamed - refactored...
//really DOES NOT need to be inide Klon!!
//in fact it's mostly inside Ready()! - don[t[ need OwnersVAlid()
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

lemma boundsNestingWiderContext(o : Object, less : set<Object>, more : set<Object>)
  requires less <= more
  requires boundsNestingOK(o,less)
  ensures  boundsNestingOK(o,more)
  {
    assert COK(o, less);
    COKWiderContext2(o, less, more);
    assert COK(o, more);

  }

lemma boundsNestingFromKlon(o : Object, context : set<Object>, prev : Klon)
  requires prev.boundsNestingOK(o,context)
  requires from(prev)
  ensures  boundsNestingOK(o,context)
  {}


lemma BoundsNestingFromCOK(o : Object, context : set<Object>)
  requires COK(o, context)
  ensures  boundsNestingOK(o, context)
  {
    reveal COK();

    // assert  ownerInsideOwner(o.owner, o.bound);
    // assert  ownerInsideOwner(o.AMFO, o.AMFB);
    // assert  ownerInsideOwner(o.AMFB, o.bound);
    // assert  ownerInsideOwner(o.AMFO, o.bound);
    // assert  ownerInsideOwnerInsideOwner(context, o.owner, o.bound);
    // assert  ownerInsideOwnerInsideOwner(context, o.AMFO, o.AMFB);
    // assert  ownerInsideOwner(o.allExternalOwners(),o.allExternalBounds());
    // assert  ownerInsideOwner(o.AMFO,o.allExternalOwners());
    // assert  ownerInsideOwner(o.AMFB,o.allExternalBounds());

    assert boundsNestingOK(o, context);
  }



lemma BoundsNestingFromReady(o : Object, context : set<Object>)
  requires o.Ready()
  requires o.AllOwnersAreWithinThisHeap(context)

// additional requs to acquire COK(o, context)
// cos bounsNesting itself ncludes COK(o, context)
/// WHICH IT SHOULDNT,,
  requires o.Valid()
  requires o in context
  requires o.AllOutgoingReferencesAreOwnership(context)

  ensures  COK(o, context)
  ensures  boundsNestingOK(o, context)
  {
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

    assert (forall oo <- o.AMFX :: oo.Ready());
    assert (o.AMFB <= o.AMFO <= context);
    assert (forall oo <- (o.AMFX), ooo <- oo.AMFO :: o.AMFO >= oo.AMFO > ooo.AMFO);

    assert COK(o, context);

    assert boundsNestingOK(o, context);
  }




method {:verify false} XXXCOKput(f : Object, context : set<Object>, n : string, t : Object)

  ensures f.fields == old(f.fields)[n:=t]
  ensures  COK(f, context)

  ensures  t.fields.Keys == old(t.fields.Keys) + {n}
  ensures  (f.fields.Keys - t.fields.Keys) < old(f.fields.Keys - t.fields.Keys)
  ensures  calid()
  ensures  old(calid())
  ensures  readyAll()
  ensures  readyOK(f)

  ensures  unchanged(f)
  ensures  unchanged(oHeap)
  ensures  unchanged(m.Values - {t})
  ensures  unchanged(m.Keys)
  ensures  unchanged(ns - {t})

  modifies f`fields
{
  COKput(f, context, n, t);
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
//  ensures  f.fields[n] == t
//  ensures  n in f.fields.Keys
//  ensures  forall x <- old(f.fields.Keys) :: f.fields[x] == old(f.fields[x])\

  ensures f.fields == old(f.fields)[n:=t]
  ensures  COK(f, context)
  modifies f`fields
{
    f.fields := f.fields[n:=t];

assert DEREK: COK(f, context) by {

    reveal COK();
    assert (f in context);
    assert (f.AMFB <= f.AMFO <= context);
    assert (forall oo <- f.AMFO :: oo.Ready());
    assert (forall o <- (f.AMFO - {f}), ooo <- o.AMFO :: f.AMFO >= o.AMFO > ooo.AMFO);
    assert (f.Ready());
    assert (f.Valid());
    assert (f.AllOutgoingReferencesAreOwnership(context));
    assert AllTheseOwnersAreFlatOK(f.AMFO - {f});

    assert f.AllFieldsContentsConsistentWithTheirDeclaration();
  //  && (f.AllOutgoingReferencesWithinThisHeap(context))

  }
  assert COK(f, context) by { reveal DEREK; }

}



  opaque function putin(k : Object, v : Object) : (r : Klon)
    //put k -> v into map, k inside o
    reads oHeap`fields, oHeap`fieldModes
    reads k`fields, k`fieldModes
    reads v`fields, v`fieldModes
    reads ns`fields, ns`fieldModes
    reads m.Values`fieldModes
    reads m.Keys`fieldModes

    requires calid()
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
    requires v.allExternalOwners() <= oHeap+ns //need to hae proceessed all owners first ************

    requires (k.owner <= m.Keys) && (mapThruKlon(k.owner, this) == v.owner)

    requires inside(k, o)
    requires v.fieldModes == k.fieldModes

    ensures  r == klonKV(this,k,v)
    ensures  klonVMapOK(r.m)
    ensures  klonVMapOK(m)
    //ensures  r == Klon(VMapKV(m,k,v), o, oHeap, ns+{v})

    ensures  v in r.ns
    ensures  k in r.m.Keys && r.m[k] == v
  ////  ensures  COK(v, r.oHeap+r.ns)
    ensures  k in r.m.Keys
    ensures  v in r.m.Values
    ensures  r.m == m[k:=v]
    ensures  mapLEQ(m, r.m)

  ensures  mapLEQ(m,r.m)
  ensures  r.m.Keys >= m.Keys + {k}
  ensures  r.m.Values >= m.Values + {v}
  ensures  r.o == o
  ensures  r.oHeap == oHeap

    ensures  klonEQ(r,klonKV(this,k,v))
    ensures  klonLEQ(this, r)
    ensures  klonVMapOK(r.m)
    ensures  klonVMapOK(m)

    ensures  r.ns == ns+nu(k,v)
    ensures  v in r.ns
    ensures  k in r.m.Keys && r.m[k] == v
//    ensures  COK(v, r.oHeap+r.ns)
    ensures  k in r.m.Keys
    ensures  v in r.m.Values
    ensures  r.m.Values == m.Values + {v}
    ensures  r.m == m[k:=v]
    ensures  mapLEQ(m, r.m)

//    ensures  r.from(this)
    ensures  AllMapEntriesAreUnique(this.m)



//     ensures  r.calid()
//     ensures  r.from(this)
    // ensures  AllMapEntriesAreUnique(this.m)
  {
    var rv := Klon(VMapKV(m,k,v), o, o_amfx, c_owner, c_amfx, oxtra, cxtra, oHeap, ns+nu(k,v));
   // var rv := klonKV(this,k,v);
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
    ensures  r == Klon(VMapKV(m,k,k), o, o_amfx,  {}, c_amfx, oxtra, cxtra, oHeap, ns)

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
    var rv := Klon(VMapKV(m,k,k), o, o_amfx, c_owner,  c_amfx, oxtra, cxtra, oHeap, ns);
    rv
    } //END putout





} ///end datatype Klon











  lemma calidObjectsKV(m0 : Klon, k : Object, v : Object, m1 : Klon)
    //given m09 valid, m1 = m0]k+b]
    requires m0.calidObjects()
//    requires klonVMapOK(m0.m)
    requires klonCanKV(m0, k, v)

    requires m1 == klonKV(m0, k, v)
    requires m1.from(m0)

    ensures  m1.calidObjects()
{
//    assert m0.calidObjects();
    reveal m0.calidObjects();

//   //unpacking m0.calidObjects();
//     assert m0.o in m0.oHeap;
//     assert m0.m.Keys <= m0.oHeap;
//     assert m0.ns !! m0.oHeap;
//     assert m0.m.Values <= m0.ns + m0.oHeap;
//     assert m0.ns <= m0.m.Values;
//
//     assert m0.o in m0.oHeap;
//     assert m1.o == m0.o;
//     assert m1.oHeap == m0.oHeap;
//     assert m1.o in m1.oHeap;
//
//     assert m0.m.Keys <= m0.oHeap;
//     assert m1.m.Keys <= m1.oHeap;
//
//     assert m0.ns !! m0.oHeap;
//     assert m1.ns !! m1.oHeap;
//
//     assert m0.m.Values <= m0.ns + m0.oHeap;
//     assert m1.m.Values <= m1.ns + m1.oHeap;
//
//     assert m0.ns <= m0.m.Values;
//     assert m1.ns <= m1.m.Values;

//    reveal m1.calidObjects();
//    assert m1.calidObjects();
}



  lemma calidObjectsKV1(m0 : Klon, k : Object, v : Object, m1 : Klon)
    //given m09 valid, m1 = m0]k+b]
    requires m0.calidObjects()
    requires klonCanKV(m0, k, v)

    requires m1 == klonKV(m0, k, v)
    requires m1.from(m0)

    ensures  m1.calidObjects()
{
    reveal m0.calidObjects();
}






  lemma calidOKKV(m0 : Klon, k : Object, v : Object, m1 : Klon)
    //given m09 valid, m1 = m0]k+b]
    requires m0.calidOK()
    requires klonCanKV(m0, k, v)

    requires m1 == klonKV(m0, k, v)
    requires m1.from(m0)

    ensures  m1.calidOK()
{
    assert m0.calidOK();
    reveal m0.calidOK();

    assert (m0.o in m0.oHeap);
    assert (m1.o in m1.oHeap);

    assert m1.m        == m0.m[k:=v];
    assert m1.m.Keys   == m0.m.Keys   + {k};
    assert m1.m.Values == m0.m.Values + {v};

    assert m1.oHeap    == m0.oHeap;
    assert m1.ns       == m0.ns + nu(k,v);

    assert (m0.m.Keys  <= m0.oHeap);
    assert (m1.m.Keys  <= m1.oHeap);


    if (k==v) {
//       assert m1.oHeap == m0.oHeap;
//       assert nu(k,v) == {};
//       assert (m0.m.Values <= m0.oHeap+m0.ns);
       assert v in m0.oHeap;
       assert (m0.m.Values+{v}) <= (m0.oHeap+m0.ns);
       assert (m1.m.Values)     <= (m1.oHeap+m1.ns);
    } else {
//       assert m1.oHeap == m0.oHeap;
//       assert nu(k,v) == {v};
//       assert m1.ns == (m0.ns + nu(k,v)) == m0.ns+{v};

//       assert (m0.m.Values <= m0.oHeap+m0.ns);
       assert v in m0.ns+{v};
       assert (m0.m.Values+{v}) <= (m0.oHeap+m0.ns+{v});
       assert (m1.m.Values)     <= (m1.oHeap+m1.ns);
    }

    assert (m1.m.Values <= m1.oHeap+m1.ns);

    assert COK(m0.o, m0.oHeap);
    assert COK(m1.o, m1.oHeap);

    assert CallOK(m0.oHeap);
    assert CallOK(m1.oHeap);

    assert CallOK(m0.m.Keys, m0.oHeap);
    assert COK(k,            m0.oHeap);
    CallOKfromCOK(k,         m0.oHeap);
    assert CallOK({k},       m0.oHeap);
    CallOKWiderFocus(m0.m.Keys, {k}, m0.oHeap);
    assert m1.m.Keys   == m0.m.Keys + {k};
    assert CallOK(m1.m.Keys, m0.oHeap);
    assert m1.oHeap == m0.oHeap;
    assert CallOK(m1.m.Keys, m1.oHeap);



    assert CallOK(m0.m.Values, m0.oHeap+m0.ns);
    assert m1.ns    == m0.ns + nu(k,v);
    if (k==v) {
      assert k in m0.oHeap;
      assert v in m0.oHeap;
      AddContainedElement(v, m0.oHeap, m0.oHeap+{v});
      assert m0.oHeap+{v} == m0.oHeap;
      // assert m0.oHeap+{v}+m0.ns == m0.oHeap+m0.ns;
      // assert m0.oHeap+m0.ns+{v} == m0.oHeap+m0.ns;
      assert m1.oHeap == m0.oHeap;
      assert m1.ns == m0.ns+nu(k,v);
      AddEmpty(m1.ns, nu(k,v), m0.ns+nu(k,v));
      assert nu(k,v) == {};
      AddEmpty(m0.ns, nu(k,v), m0.ns+nu(k,v));
      assert m0.ns + nu(k,v) == m0.ns;
      assert m0.ns  == m1.ns;
ISFUCKEDYEAH(m0.oHeap, m0.ns, v);
      assert m0.oHeap+m0.ns+{v} == m0.oHeap+m0.ns;
      assert m0.oHeap+m0.ns+{v} == m1.oHeap+m1.ns;
    } else {
      assert k != v;
      funuf(k,v);
      assert nu(k,v) == {v};
      assert m1.ns == m0.ns+nu(k,v);
      assert m1.ns == m0.ns+{v};
      assert m1.oHeap == m0.oHeap;
ISFUCKEDNAAA(m0.oHeap,m1.oHeap,m0.ns,m1.ns,v);
      assert (m0.oHeap)+(m0.ns+{v}) == m1.oHeap+m1.ns;
    }
    assert       m0.oHeap+m0.ns+{v} == m1.oHeap+m1.ns;
    assert CTXT: m0.oHeap+m0.ns+{v} == m1.oHeap+m1.ns;

    assert CallOK(m0.m.Values,           m0.oHeap+m0.ns);
    CallOKWiderContext(m0.m.Values, m0.oHeap+m0.ns, {v});
    assert CallOK(m0.m.Values,           m0.oHeap+m0.ns+{v});

    assert m0.boundsNestingOK(v,         m0.oHeap+m0.ns+{v});
    assert COK(v,                        m0.oHeap+m0.ns+{v});
    CallOKfromCOK(v,                     m0.oHeap+m0.ns+{v});
    assert CallOK({v},                   m0.oHeap+m0.ns+{v});

    CallOKWiderFocus(m0.m.Values, {v},   m0.oHeap+m0.ns+{v});
    assert CallOK(m0.m.Values+{v},       m0.oHeap+m0.ns+{v});

    assert m1.m.Values == m0.m.Values + {v};
    assert CallOK(m1.m.Values,   m0.oHeap+m0.ns+{v});
    assert CallOK(m1.m.Values,   m1.oHeap+m1.ns);


    assert m0.oHeap+m0.ns+{v} == m1.oHeap+m1.ns;
    assert m1.ns == m0.ns + nu(k,v);
    assert COK(v,m0.oHeap+m0.ns+{v});
    assert COK(v,m1.oHeap+m1.ns);
    CallOKfromCOK(v,m1.oHeap+m1.ns);
    assert CallOK({v},m1.oHeap+m1.ns);

    assert CallOK(m0.ns, m0.oHeap+m0.ns);
    CallOKWiderContext2(m0.ns,m0.oHeap+m0.ns, m1.oHeap+m1.ns);
    assert CallOK(m0.ns, m1.oHeap+m1.ns);
    assert CallOK({v},m1.oHeap+m1.ns);
    CallOKWiderFocus(m0.ns, {v},m1.oHeap+m1.ns);
    assert CallOK(m1.ns, m1.oHeap+m1.ns);

    assert forall x <- m0.oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m0.oHeap);
    assert forall x <- m1.oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m1.oHeap);

    reveal m1.calidOK();
    assert m1.calidOK();
}


lemma ISFUCKEDYEAH(H : set<Object>, N : set<Object>,  v :  Object)
 requires v in H
 ensures (H + N + {v}) == (H + N)
 {}

lemma ISFUCKEDNAAA(H0 : set<Object>, H1 : set<Object>,
                   N0 : set<Object>, N1 : set<Object>,
                    v :  Object)
  requires H1 == H0
  requires N1 == N0+{v}
  ensures  H0+N0+{v} == H1+N1
 {}



  lemma {:timeLimit 25} calidMapKV(m0 : Klon, k : Object, v : Object, m1 : Klon)
    //given m09 valid, m1 = m0]k+b]
    requires m0.calidObjects() && m0.calidOK()
    requires m0.calidMap()
    requires klonCanKV(m0, k, v)

    ///////////////////////////////  WHOOP WHOOP DA SOUND OF DA POLICE
    requires canMapOwnersThruKlown(k,m1)
    requires canKlown(m0, k, v, m1)
    ///////////////////////////////  WHOOP WHOOP DA SOUND DAT I MISS


    requires m1 == klonKV(m0, k, v)
    requires m1.from(m0)

    ensures  m1.calidObjects() && m1.calidOK()
    ensures  m1.calidMap()
{
    reveal m0.calidMap();

    calidObjectsKV(m0,k,v,m1);
    calidOKKV(m0,k,v,m1);

    assert m1.calidObjects() && m1.calidOK();

    assert AllMapEntriesAreUnique(m1.m);
    assert klonVMapOK(m1.m);
    assert (forall x <- m1.m.Keys ::
        && m1.boundsNestingOK(x, m1.oHeap));

    forall x <- m1.m.Keys
       ensures (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns))
       {
         if (x in m0.m.Keys) {
            assert (m0.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns));
assert COK(m0.m[x], m0.oHeap+m0.ns);
assert m1.m[x] ==  m0.m[x];
assert COK(m1.m[x], m0.oHeap+m0.ns);
assert (m1.oHeap+m1.ns) >= (m0.oHeap+m0.ns);
COKWiderContext2(m1.m[x],m0.oHeap+m0.ns, m1.oHeap+m1.ns);
assert COK(m1.m[x], m1.oHeap+m1.ns);

            assert (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));
         } else
          {
            assert x == k;
            assert m1.m[k] == v;

var lleft := m0.oHeap+m0.ns+{v};
var rrite := m1.oHeap+m1.ns;
assert       m0.oHeap+m0.ns+{v} == m1.oHeap+m1.ns;
assert                    lleft == rrite;

assert v in lleft;
assert COK(v, lleft);


COKWiderContext2(v,lleft, rrite);
assert COK(v, rrite);

         assert (m1.boundsNestingOK(v, rrite));


        assert (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));

//       assuage (m1.boundsNestingOK(m1.m[x], m1.oHeap+m1.ns));
          }
       }

    assert (forall x <- m1.m.Keys ::
        && m1.fieldMappingsOK(x, m1.m[x], m1.m.Keys));
    assert klonAllOwnersAreCompatible(m1);

    assert (forall x <- m0.m.Keys :: (not(inside(x,m0.o)) ==> (m0.m[x] == x)));
    assert (not(inside(k,m0.o)) ==> (k==v));

    forall x <- m1.m.Keys
       ensures (not(inside(x,m1.o)) ==> (m1.m[x] == x))
       {
          if (x in m0.m.Keys)
            { assert (not(inside(x,m0.o)) ==> (m0.m[x] == x));
              assert (not(inside(x,m1.o)) ==> (m1.m[x] == x));
            } else {
              assert (x == k);
              assert ((v==k) == (outside(k, m0.o)));
              assert ((v==k) == (outside(k, m1.o)));
              assert  m1.m[k] == v;
              assert (not(inside(x,m1.o)) ==> (m1.m[k] == v));
              assert (not(inside(x,m1.o)) ==> (m1.m[x] == x));
            }
       }
    assert (forall x <- m1.m.Keys :: (not(inside(x,m1.o)) ==> (m1.m[x] == x)));


    assert m1.calidMap();  //dunno if/why this 4rrors out
}

predicate canKlown(m0 : Klon, k : Object, v : Object, m1 : Klon)
  //predicate collecting all the extra preconditiosn from previous version of klonCalidKVCalid...

  requires canMapOwnersThruKlown(k,m1) //YEAH. M1. FUCKED INNIT.
//ript from klonKV
  reads m0.m.Values`fieldModes
  reads m0.m.Keys`fieldModes
  reads k`fields, k`fieldModes
  reads v`fields, v`fieldModes
  reads m0.oHeap`fields, m0.oHeap`fieldModes
  reads m0.ns`fields, m0.ns`fieldModes

{
  && ((v==k) == (outside(k, m0.o)))
  && ((v!=k) ==> (v.fields == map[])) //KJX FRI20DEC - new objects being added need to be empty?

  && mappingOwnersThruKlownOK(k,m1) //THIS iS A BIT WEIRD as a requires.. but

  && (forall o <- m0.m.Keys :: m0.readyOK(o))
}

  lemma {:timeLimit 3605} calidSheepKV(m0 : Klon, k : Object, v : Object, m1 : Klon)
    //given m09 valid, m1 = m0]k+b]
    requires m0.calidObjects() && m0.calidOK()
    requires m0.calidSheep()
    requires klonCanKV(m0, k, v)

    requires m1 == klonKV(m0, k, v)
    requires m1.from(m0)

    ///////////////////////////////  WHOOP WHOOP DA SOUND OF DA POLICE
    requires canMapOwnersThruKlown(k,m1)
    requires canKlown(m0, k, v, m1)
    ///////////////////////////////  WHOOP WHOOP DA SOUND DAT I MISS

    ensures  m1.calidObjects() && m1.calidOK()
    ensures  m1.calidSheep()
{
    reveal m0.calidSheep();
    calidObjectsKV(m0,k,v,m1);
    calidOKKV(m0,k,v,m1);

    assert m1.calidObjects() && m1.calidOK();

    reveal m1.calidObjects();  assert m1.calidObjects();
    reveal m1.calidOK();       assert m1.calidOK();
    reveal m1.AreWeNotMen();

    forall x <- m1.m.Keys
      ensures (m1.AreWeNotMen(x, m1)) //by
    {
      if (x in m0.m.Keys) {
           assert m0.AreWeNotMen(x, m0);
           assert x != k;

//     assert (   (inside(x,m0.o)) ==> (m0.m[x] in m0.ns));
//     assert (not(inside(x,m0.o)) ==> (m0.m[x] == x));
//     assert (   (inside(x,m0.o)) ==> (UniqueMapEntry(m0.m,x)));
//     assert (not(inside(x,m0.o)) ==> (UniqueMapEntry(m0.m,x)));
//
//     assert m1.m[x] == m0.m[x];
//
    assert (   (inside(x,m1.o)) ==> (m1.m[x] in m1.ns));
    assert (not(inside(x,m1.o)) ==> (m1.m[x] == x));
    assert (   (inside(x,m1.o)) ==> (UniqueMapEntry(m1.m,x)));
    assert (not(inside(x,m1.o)) ==> (UniqueMapEntry(m1.m,x)));

           assert m1.AreWeNotMen(x, m1);
//           assume m1.AreWeNotMen(x, m1);
      } else {
          assert x == k;

    assert (   (inside(x,m1.o)) ==> (m1.m[x] in m1.ns));
    assert (not(inside(x,m1.o)) ==> (m1.m[x] == x));
    assert (   (inside(x,m1.o)) ==> (UniqueMapEntry(m1.m,x)));
    assert (not(inside(x,m1.o)) ==> (UniqueMapEntry(m1.m,x)));

           assert m1.AreWeNotMen(x, m1);
//             assume m1.AreWeNotMen(x, m1);

      }
    }

    assert (forall x <- m1.m.Keys :: m1.AreWeNotMen(x, m1));




    assert (forall x <- m1.m.Keys :: x.fieldModes == m1.m[x].fieldModes);
    assert AllMapEntriesAreUnique(m1.m);

    assert m1.calidSheep();
}






  lemma calidKV(m0 : Klon, k : Object, v : Object, m1 : Klon)
    //given m09 valid, m1 = m0]k+b]
    requires m0.calid()
    requires klonCanKV(m0, k, v)

    requires m1 == klonKV(m0, k, v)
    requires m1.from(m0)

    ///////////////////////////////  WHOOP WHOOP DA SOUND OF DA POLICE
    requires canMapOwnersThruKlown(k,m1)
    requires canKlown(m0, k, v, m1)
    ///////////////////////////////  WHOOP WHOOP DA SOUND DAT I MISS


    ensures  m1.calid()
{
    reveal m0.calid();

    calidObjectsKV(m0,k,v,m1);
    calidOKKV(m0,k,v,m1);
    calidMapKV(m0,k,v,m1);
    calidSheepKV(m0,k,v,m1);
}



















































































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


lemma NUKV(k : Object, v : Object, r : set<Object>)
  requires (r == nu(k,v))
  ensures  (k==v) ==> (r == {})
  ensures  (k!=v) ==> (r == {v})
{}

  function NUK2(b : bool, v : Object) : set<Object>
  {
    if (b) then {} else {v}
  }


  function nu(k : Object, v : Object) : set<Object>
    ///if adding k:=v to a klon, this is what gets added to ns and to m.values
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

  lemma funuf(k : Object, v : Object)
    requires k != v
    ensures  nu(k,v) == {v}
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












// method Clone_Inside_World(a : Object, m0 : Klon)
//   returns (b : Object, m : Klon)
//   decreases (m0.oHeap - m0.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_World(


function mapThruKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  //image of os under klon mapping m
  // reads m.m.Keys`fields, m.m.Keys`fieldModes
  // reads m.m.Values`fields, m.m.Values`fieldModes
  requires os <= m.m.Keys
{ set o <- os :: m.m[o] }


//
// function mapThruKlon(os: set<Object>, m : Klon) : (r : set<Object>)
//   //image of os under klon mapping m
//   //currently doesn't require calid, to avoid circular reasonings
//   //but can reason through calid. which is probalby bad,really
//   //be bettter to split off as a lemma...
//
//   // reads m.oHeap`fields, m.oHeap`fieldModes
//   // reads m.ns`fields, m.ns`fieldModes
// //requires m.calid()  (does it or doesn't it?)
//   requires os <= m.m.Keys
//
//   ensures m.calid() ==> (r  <= m.m.Values <= (m.oHeap + m.ns))  //Hmm. not great but...
//   ensures m.calid() ==> (CallOK(r, (m.oHeap + m.ns))) //ditto. or should they be lemmas..?
// {
//   var r := set o <- os :: m.m[o];
//
//   reveal m.calid(), m.calidOK();
//   assert m.calid() ==> (r  <= m.m.Values <= (m.oHeap + m.ns));
//
//   reveal COK(), CallOK();
//   assert m.calid() ==> (CallOK(r, (m.oHeap + m.ns)));
//
//   r
// }

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
//  requires o in m.m.Keys
//  requires c == m.m[o]
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


//
// lemma klonSameOwnersAreCompatible(o : Object, m : Klon)
//    ensures klonOwnersAreCompatible(o,o,m)
// {}


predicate klonAllOwnersAreCompatible( m : Klon, ks: set<Object> := m.m.Keys)
//
requires ks <= m.m.Keys

reads m.oHeap`fields,      m.oHeap`fieldModes
reads m.ns`fields,         m.ns`fieldModes
reads m.m.Keys`fields,     m.m.Keys`fieldModes
reads m.m.Values`fields,   m.m.Values`fieldModes
  {
    forall o <- ks :: klonOwnersAreCompatible(o,m.m[o],m)
  }


lemma  klonOwnersAreCompatibleWider(o : Object, c : Object, m0 : Klon, m : Klon)
  requires o in m0.m.Keys
  requires c == m0.m[o]
  requires klonOwnersAreCompatible(o, c, m0)
  //requires m0.calid()
  //requires m.from(m0)
  requires mapGEQ(m.m, m0.m)
  requires m.o     == m0.o
  requires m.oHeap == m0.oHeap
  requires m.ns    >= m0.ns
  ensures  klonOwnersAreCompatible(o, c, m)
{
  assert
      && m.boundsNestingOK(o, m0.oHeap)
      && m.boundsNestingOK(c, m0.oHeap+m0.ns)
      && (c.AMFO >= c.AMFB >= o.AMFB)
      ;

    m.boundsNestingWiderContext(o, m0.oHeap, m.oHeap);
    m.boundsNestingWiderContext(c, m0.oHeap+m0.ns, m.oHeap+m.ns);

  assert
      && m.boundsNestingOK(o, m.oHeap)
      && m.boundsNestingOK(c, m.oHeap+m.ns)
      && (c.AMFO >= c.AMFB >= o.AMFB)
      ;

  assert klonOwnersAreCompatible(o, c, m);
}





lemma  klonOwnersAreCompatibleKV(o : Object, c : Object, m0 : Klon, m : Klon)
  requires o !in m0.m.Keys
  requires klonOwnersAreCompatible(o, c, m0)
  //requires m0.calid(
  //requires m.from(m0)
  requires mapGEQ(m.m, m0.m)
  requires m.o     == m0.o
  requires m.oHeap == m0.oHeap
  requires m.ns    >= m0.ns
  ensures  klonOwnersAreCompatible(o, c, m)
{
  assert
      && m.boundsNestingOK(o, m0.oHeap)
      && m.boundsNestingOK(c, m0.oHeap+m0.ns)
      && (c.AMFO >= c.AMFB >= o.AMFB)
      ;

    m.boundsNestingWiderContext(o, m0.oHeap, m.oHeap);
    m.boundsNestingWiderContext(c, m0.oHeap+m0.ns, m.oHeap+m.ns);

  assert
      && m.boundsNestingOK(o, m.oHeap)
      && m.boundsNestingOK(c, m.oHeap+m.ns)
      && (c.AMFO >= c.AMFB >= o.AMFB)
      ;

  assert klonOwnersAreCompatible(o, c, m);
}




lemma klonFieldsAreCompatible(of : Object, ot : Object, cf : Object, ct: Object, m : Klon)
{}

lemma klonSameOwnersAreCompatible(o : Object, c : Object, m1 : Klon)
  requires o == c
  requires (o in m1.m.Keys) && (m1.m[o] == c)
  requires COK(o,m1.oHeap)
  requires m1.boundsNestingOK(o, m1.oHeap)
  ensures  m1.boundsNestingOK(c, m1.oHeap+m1.ns)
  ensures  klonOwnersAreCompatible(o, c, m1)
{
  assert m1.boundsNestingOK(o, m1.oHeap);
  m1.boundsNestingWiderContext(o,  m1.oHeap, m1.oHeap+m1.ns);
  assert (c.AMFO >= c.AMFB >= o.AMFB);

  assert klonOwnersAreCompatible(o, c, m1);
 }







lemma klonAllRefsKVOK(k : Object, v : Object, m0 : Klon, m : Klon)
//can add k,v to m0 yeilding m
//andn lal refs are OK
  requires m0.readyAll()
  requires allMapOwnersThruKlownOK(m0)
  //requires m0.calid()
  requires klonCanKV(m0,k,v)
  requires m == klonKV(m0,k,v)
  requires m.m.Keys == m0.m.Keys+{k}
  requires m.m.Values == m0.m.Values+{v}
  requires m.m[k] == v
  requires m.m == m0.m[k:=v]

  requires k.Ready()
  requires k !in m0.m.Keys
  requires v !in m0.m.Values
  requires m0.ownersInKlown(k)

requires m.m.Keys >= k.bound
requires m.m.Keys >= k.ntrnl > k.owner >= k.bound  //IN-KLON
requires m.m.Keys >= k.AMFO  > k.AMFX  >= k.AMFB   //IN-KLON
requires k.owner <= m.m.Keys   //IN-KLON
requires k.AMFO  <= m.m.Keys   //IN-KLON


  //preconds or allMapOwnersThruKlownOK(m)
  requires m == klonKV(m0,k,v)
  requires k.owner <= m.m.Keys   //IN-KLON
  requires k.AMFO  <= m.m.Keys   //IN-KLON
  // requires mappingOwnersThruKlownOK(k,m)


  //this one of course...
  //  requires forall ot <- (m0.m.Keys + {k}) ::  klonRefOK(k,ot,v,m.m[ot],m)

//  ensures  mappingOwnersThruKlownOK(k,m)
//  ensures  m.readyAll()
//  ensures  allMapOwnersThruKlownOK(m)
{
  assert k !in m0.m.Keys;

  assert mapGEQ(m.m,m0.m);

//   assert  forall of <- m0.m.Keys, ot <- m0.m.Keys ::
//      var cf := m0.m[of];
//      var ct := m0.m[ot];
//       false; //TODO
// //     klonRefOK(of,ot,cf,ct,m0);
//

///////////////////////////////////////////////////
///////////////   (m0,k,v,m);
///////////////////////////////////////////////////

//what on earth is this chuink doing (and how is it doing it?)
        //   assert (forall of <- m0.m.Keys, ot <- m0.m.Keys ::
        //             (var cf := m0.m[of];  assert cf == m.m[of];
        //             (var ct := m0.m[ot];  assert ct == m.m[ot];
        //               true))); //TODO
  //   klonRefOK(of,ot,cf,ct,m) == klonRefOK(of,ot,cf,ct,m0);

//NEED EXISTENTIONALITY HERE   TODO
//very much so!


//
//   assert forall of <- m.m.Keys, ot <- m.m.Keys ::
//      var cf := m.m[of];
//      var ct := m.m[ot];
//
//     if ((of in m0.m.Keys) && (ot in m0.m.Keys))
//        then  (klonRefOK(of,ot,cf,ct,m0))
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

  requires r.readyAll()
  requires allMapOwnersThruKlownOK(r)
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
          && r.readyAll()
          && allMapOwnersThruKlownOK(r)
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






lemma NoKeyNoProblems(ks : set<Object>, m0 : Klon, k : Object, v : Object)
    requires m0.calid()
    requires ks <= m0.m.Keys
    requires k !in m0.m.Keys
    requires k !in ks
    requires v !in m0.m.Values
    requires canVMapKV(m0.m, k, v)     /// rather than klonCanKV
    ensures  mapThruVMapKV(ks, m0.m, k, v) == mapThruVMap(ks, m0.m)
  //  ensures  mapThruKlonKV(ks, m0, k, v) == mapThruKlon(ks, m0)
    {
assert canVMapKV(m0.m, k, v);
IfImNotTheExtraKeyTheUnderlyingMapIsFine(ks, m0.m, k, v);
assert mapThruVMapKV(ks, m0.m, k, v) == mapThruVMap(ks, m0.m);
///  mapThruVMapIsMapThruKlon(ks, m0, mapThruVMap(ks,  m0.m));
assert mapThruVMap(ks, m0.m) == mapThruKlon(ks, m0);
//assert mapThruKlonKV(ks, m0, k, v) == mapThruKlon(ks, m0);

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
//  assuage b.AMFO  <= m.m.Values;
  m.boundsNestingFromCalid(b, m.oHeap+m.ns);
}





///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
//spare/old cloning methods



//
// method OLDEClone_Via_Map(a : Object, m0 : Klon)
//   returns (b : Object, m : Klon)
//   //entry point for Clone - clones a according to map m0
//   //call with m0 empty
//   decreases (m0.oHeap - m0.m.Keys), a.AMFO, (a.fields.Keys), 20 //Klone_Via_Map
//
//   requires m0.calid()
//   requires a in m0.oHeap  //technically redundant given COKx
//   requires COK(a, m0.oHeap) //ties owners into OHEAP but not KLON MAP
//
//  //FROMHERE
//   ensures  m.calid()
//
//   ensures  a in m.m.Keys
//   ensures  m.m[a] == b
//   ensures  m.m[a] == b
//   ensures  b in m.m.Values
// //  ensures  COK(b,m.oHeap+m.ns)
//
//   //should I package this up - as aw twostate or a onestate?
//   ensures  mapLEQ(m0.m,m.m)
//   ensures  m.m.Keys >= m0.m.Keys + {a}
//   ensures  m.m.Values >= m0.m.Values + {b}
//   ensures  m.from(m0)
//
//   ensures  m.o == m0.o
//   ensures  m.oHeap == m0.oHeap
//   ensures  m.ns >= m0.ns
//   //  ensures  if (inside(a, m0.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures  klonVMapOK(m.m)
//   ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//   // should we say something about b.AMFO?  b.AMFO <= m.m.Values? por again m.hasV(b)?
//   // m.key(a)?  m.val(a)???
//   // should decided whether to do this with AMFOs or owners
//   // and don one one...
//   //OK os THIS requires us to make sure all the owners are in (even if outsidef - where does that happen?)
//   ensures  m.from(m0)
//   //ensures b.AMFO == mapThruKlon(a.AMFO, m) //hmmm - bit it's NOT there
//
//   // ensures  a !in m0.m.Keys ==> b !in m0.ns  //KJX sure about this?
//   ensures  unchanged(a)
//   ensures  unchanged(m0.oHeap)
//   ensures  unchanged(m0.ns)
//
//   ensures klonOwnersAreCompatible(a, b, m)
//
//   ensures b.fieldModes == a.fieldModes
//
// //TOHERE
//
//   //  ensures  fresh(b)
//   //modifies m0[a]
//   //  modifies m0.ns`fields //argh. pity so wide
//   //modifies (set o : Object | o !in (m0.oHeap+m0.ns))`fields
//   // modifies (set o : Object | o !in (m0.oHeap+m0.ns))`fields
//   modifies {} // just modifes objecst allocated after this point?
// {
//   m := m0;
//
//   assert m.calid();
//   assert MCALID: m.calid();
//
//   assert  m.o     == m0.o;
//   assert  m.oHeap == m0.oHeap;
//   assert  m.ns    >= m0.ns;
//
//   assert unchanged(a) && unchanged(m.oHeap);
//
//   print "CALL Clone_Via_Map:", fmtobj(a), " pivot:", fmtobj(m.o), "\n";
//
//   print "VARIANT CVM ", |(m0.oHeap - m0.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 20, "\n";
//
//   assert COKSTART: COK(a, m.oHeap);
//
//   print "Clone_Via_Map started on:", fmtobj(a), "\n";
//
//   //if already in hash table - return it and be done!
//   //not sure why this takes sooo long compared to other
//
//   //at some point - double check that the ubvaruabnts
//   /// mean if a in m.m.Keys, a.AMFO in m.m.Keys too...
//   /// not least because that pushes b into m.m.Values...
//   if (a in m.m.Keys) {
//
//             assert (a in m.m.Keys) by {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               assert m.m.Keys == m.m.Keys;
//             }
//
//             b := m.m[a];
//
//             assert (b in m.m.Values) by {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               assert b == m.m[a];
//               assert b in m.m.Values;
//               assert m.m.Values == m.m.Values;
//               assert b in m.m.Values;
//             }
//
//             assert CallOK(m.m.Values, m.oHeap+m.ns) by
//             {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               reveal m.calidOK();
//               assert m.calidOK();
//             }
//
//             COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
//             assert COK(b, m.oHeap+m.ns);
//
//
//
//
//             assert klonVMapOK(m.m) && (a.AMFO <= m.m.Keys)  by
//             {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidOK();
//               assert m.calidOK();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               reveal m.calidMap();
//               assert m.calidMap();
//               assert m.m.Keys == m.m.Keys;
//               assert klonVMapOK(m.m) && a.AMFO <= m.m.Keys;
//               assert klonVMapOK(m.m) && a.AMFB <= m.m.Keys;
//             }
//
//             reveal m.calid();
//             assert m.calid();
//             reveal m.calidSheep();
//             assert m.calidSheep();
//
//             assert  b.fieldModes == a.fieldModes;
//             assert  m.o     == m0.o;
//             assert  m.oHeap == m0.oHeap;
//             assert  m.ns    >= m0.ns;
//             //  reveal  m.from();
//
//
//           assert klonOwnersAreCompatible(a, b, m) by {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidOK();
//               assert m.calidOK();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               reveal m.calidMap();
//               assert m.calidMap();
//
//               assert klonAllOwnersAreCompatible(m);
//
//               assert klonOwnersAreCompatible(a, b, m);
//
//
//
//           }
//
//
//             print "RETN Clone_Via_Map: ", fmtobj(a)," already cloned,  returning ",fmtobj(b), "\n";
//
//
//
//             return;
//   } // a in m.Keys, already cloned
//
//   assert unchanged(a) && unchanged(m.oHeap);
//
//   assert a !in m.m.Keys;
//   assert a !in m0.m.Keys;
//
//   // assert a !in m.m.Values;
//   // assert a !in m0.m.Values;
//
// ///case analysis...
//   if (outside(a,m.o)) {
//     print "Clone_Via_Map ", fmtobj(a), " is really outside ", fmtobj(m.o), "so maps to itself (share not clone)\n";
//
//       assert  //KJX keeping this for now but...
//         && (a !in m.m.Keys)
//         && (a !in m.ns)
//       by {
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
//         assert a !in m.m.Keys;
//         assert a in m.oHeap;
//         assert m.oHeap !! m.ns;
//         assert a !in m.ns;
//       }
//
//       m.WeAreDevo();
//
//     assert not(inside(a,m.o));
//     assert a !in m.m.Keys;
//     assert m.calid();
//     assert forall k <- m.m.Keys :: m.AreWeNotMen(k,m);
//     assert a  in m.oHeap;
//     assert a !in m.ns;
//
//       Klon.AintNoSunshine(a,m);
//
//
//
//       print "Hey Baby let's CLONE Outside\n";
//
//       b := a;
//
//   assert b.fieldModes == a.fieldModes;
//
//       print "Yay babhy hyou got that done\n";
//
//
//   assert a !in m.m.Keys;
//   assert a in m.oHeap;
//   assert m.oHeap !! m.ns by {
//     reveal m.calid();
//     assert m.calid();
//     reveal m.calidObjects();
//     assert m.calidObjects();
//     assert m.oHeap !! m.ns;
//   }
//   assert outside(a,m.o);
//
//
//   {
//     reveal m.calid();
//     assert m.calid();
//     reveal m.calidOK();
//     assert m.calidOK();
//     assert CallOK(m.oHeap);
//     a.CallMyOwnersWillWitherAway(a, m.oHeap);
//   }
//
//
//   {
//     reveal m.calid();
//     assert m.calid();
//     reveal m.calidObjects();
//     assert m.calidObjects();
//     assert m.m.Keys <= m.oHeap;
//     OutsidersArentMapValues(a,m);
//   }
//
//   reveal m.calidMap();
//   assert m.calidMap();
//   assert klonVMapOK(m.m);
//   assert (forall x <- m.m.Keys, oo <- x.AMFO :: oo in m.m.Keys);
//   assert (forall x <- m.m.Keys :: x.allExternalOwners() <= m.m.Keys);
//
//   assert a !in m.m.Values;
//
//   print "about to Clone_All_Owners()...";
//
//   ///////////////////////////////////////////////////////////////
//   var mc := Clone_All_Owners(a, m);
//   ///////////////////////////////////////////////////////////////
//
//   assert mc.from(m);
//   assert a.owner <= mc.m.Keys;
//   assert a.allExternalOwners() <= mc.m.Keys;
//   assert mc.calid();
//
//   m := mc;
//
//   assert a.allExternalOwners() <= m.m.Keys;
//
//   print "done clone all owners\n";
//
//
// // / /  / / / / / / / / / / / / / / / / / / / / / / / / / / / /
// // EVIL - compiedin from above
// // / /  / / / / / / / / / / / / / / / / / / / / / / / / / / / /
//
//
//   //if already in hash table - return it and be done!
//   //not sure why this takes sooo long compared to other
//
//   //at some point - double check that the ubvaruabnts
//   /// mean if a in m.m.Keys, a.AMFO in m.m.Keys too...
//   /// not least because that pushes b into m.m.Values...
//   if (a in m.m.Keys) {
//
//             assert (a in m.m.Keys) by {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               assert m.m.Keys == m.m.Keys;
//             }
//
//             b := m.m[a];
//
//             assert (b in m.m.Values) by {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               assert b == m.m[a];
//               assert b in m.m.Values;
//               assert m.m.Values == m.m.Values;
//               assert b in m.m.Values;
//             }
//
//             assert CallOK(m.m.Values, m.oHeap+m.ns) by
//             {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               reveal m.calidOK();
//               assert m.calidOK();
//             }
//
//             COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
//             assert COK(b, m.oHeap+m.ns);
//
//
//
//
//             assert klonVMapOK(m.m) && (a.AMFO <= m.m.Keys)  by
//             {
//               reveal m.calid();
//               assert m.calid();
//               reveal m.calidOK();
//               assert m.calidOK();
//               reveal m.calidObjects();
//               assert m.calidObjects();
//               reveal m.calidMap();
//               assert m.calidMap();
//               assert m.m.Keys == m.m.Keys;
//               assert klonVMapOK(m.m) && a.AMFO <= m.m.Keys;
//               assert klonVMapOK(m.m) && a.AMFO <= m.m.Keys;
//             }
//
//             reveal m.calid();
//             assert m.calid();
//             reveal m.calidSheep();
//             assert m.calidSheep();
//
//             assert  b.fieldModes == a.fieldModes;
//             assert  m.o     == m0.o;
//             assert  m.oHeap == m0.oHeap;
//             assert  m.ns    >= m0.ns;
//             //  reveal  m.from();
//
//             print "RETN Clone_Via_Map: ", fmtobj(a)," already cloned,  returning ",fmtobj(b), "\n";
//
//             return;
//   } // a in m.Keys, already cloned
//
//
//
//
// // / /  / / / / / / / / / / / / / / / / / / / / / / / / / / / /
// // EEND - compiedin from above
// // / /  / / / / / / / / / / / / / / / / / / / / / / / / / / / /
//
//   assert a !in m.m.Keys;
//   assert m.calid();
//
//
//   assert a.allExternalOwners() <= m.m.Keys;
//
//     {
//     reveal m.calid();
//     assert m.calid();
//     reveal m.calidObjects();
//     assert m.calidObjects();
//     assert m.m.Keys <= m.oHeap;
//     OutsidersArentMapValues(a,m);
//   }
//
//   print "about to putOutside...";
//
// assert  //James wonders if this shojuldb'e be AFTER the putoutside  ikt perhas that tdoesn't work
// //  && canVMapKV(m.m, a, a)
//   && (a in m.oHeap)  //KJX do I want this here?
//   && (a.allExternalOwners() <= m.m.Keys)   //merging in objectage Spike
//   && (a.AMFX <= m.m.Keys)                  //merging in objectage Spike
//   && (a.Ready())                          //merging in objectage Spike
//   && (a.AMFO == a.AMFX + {a})              //merging in objectage Spike
//   && (a.AMFO <= m.m.Keys+{a})              //merging in objectage Spike
// //  && (mapThruVMapKV(a.AMFO, m.m, a, a) == a.AMFO)
// //  && (a.owner <= a.AMFO)
//     && (a.owner <= m.m.Keys+{a})
//
//   && (a.fieldModes == a.fieldModes)
// by {
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
//
//
// }
//
// //already have this!
// //OutsidersArentMapValues(a,m);
//
// assert outside(a, m.o);
//
//
// RVfromCallOK(m.oHeap, m.oHeap);
// assert a in m.oHeap;
// assert m.o in m.oHeap;
// assert a.Ready() && a.Valid();
// assert m.o.Ready() && m.o.Valid();
//
// OwnersAreOutsideFuckers(a, m.o);
//
// // assert NIGEL:
//   // && forall oo <- a.owner :: outside(oo,m.o)
//   // && forall oo <- a.AMFO  :: outside(oo,m.o)
//   // && forall oo <- a.allExternalOwners() :: outside(oo,m.o)
//   // && (mapThruVMap(a.owner, m.m) == a.owner)
//   // && (mapThruVMapKV(a.owner, m.m, a, a) == a.owner)//KJXOWNERS
//     // && (mapThruVMapKV(a.AMFO, m.m, a, a)  == a.AMFO)
// //  && forall oo <- a.AMFO  :: m.m[oo] == oo
// //   by {
// //         reveal m.calid();
// //         assert m.calid();
// //         reveal m.calidOK();
// //         assert m.calidOK();
// //         reveal m.calidObjects();
// //         assert m.calidObjects();
// //         reveal m.calidMap();
// //         assert m.calidMap();
// //         reveal m.calidSheep();
// //         assert m.calidSheep();
// //
// //         assert forall oo <- a.allExternalOwners()  :: oo in m.m.Keys;
// //         assert forall oo <- a.allExternalOwners()  :: m.m[oo] == oo;
// //         assert forall oo <- a.owner :: outside(oo,m.o);
// //         assert forall oo <- a.owner :: m.m[oo] == oo;
// //         assert (set oo <- a.owner :: m.m[oo]) == a.owner;
// //         assert mapThruVMap(a.owner, m.m) == a.owner;
// //
// //         assert forall oo <- a.AMFO :: (oo == a) || outside(oo,m.o);
// //         assert forall oo <- a.AMFO :: (oo == a) || m.m[oo] == oo;
// //         assert (set x <- {a} :: x) == {a};
// //
// //         MapThruIdentity((a.AMFO - {a}), m.m);
// //         assert (set x <- (a.AMFO - {a}) :: m.m[x]) ==  (a.AMFO - {a});
// //
// //         IdentityExtensionality(a.AMFO - {a}, m.m, a);
// //         assert (a.AMFO - {a})+{a} == (a.AMFO);
// //         MapThruIdentity(a.AMFO, VMapKV(m.m,a,a));
// //         assert mapThruVMapKV(a.AMFO, m.m, a, a) == a.AMFO;
// //
// //         assert forall oo <- a.AMFO  :: outside(oo,m.o);
// //         assert a.owner <= a.AMFO;
// //         assert forall oo <- a.owner :: outside(oo,m.o);
// //
// //   assert forall oo <- a.owner :: outside(oo,m.o);
// //   assert forall oo <- a.AMFO  :: outside(oo,m.o);
// //   assert forall oo <- a.allExternalOwners() :: outside(oo,m.o);
// //   assert (mapThruVMap(a.owner, m.m) == a.owner);
// //   assert a !in a.owner;
// //   IfImNotTheExtraKeyTheUnderlyingMapIsFine(a.owner, m.m, a, a);
// //   assert (mapThruVMapKV(a.owner, m.m, a, a) == a.owner);
// //
// //   assert (mapThruVMapKV(a.AMFO, m.m, a, a) == a.AMFO);
// //
// //   }
//
//
//
//   // assert DEREK: (mapThruVMapKV(a.AMFO, m.m, a, a)  == a.AMFO)
//   //   by { reveal NIGEL; }
//
// assert klonCanKV(m, a, a) by {
//
// assert (a == b);
//
//   // reveal DEREK;
//   //body of klonCanKN expanded inline
//   assert canVMapKV(m.m, a, a);
//   assert (a in m.oHeap);
//   assert (if (a==a) then (a in m.oHeap) else (a !in m.oHeap));
//   assert (a.owner <= m.m.Keys+{a});
// //  assert (mapThruVMapKV(a.owner, m.m, a, a) == a.owner);
//   assert (a.AMFO <= m.m.Keys+{a});
// //  assert (mapThruVMapKV(a.AMFO, m.m, a, a) == a.AMFO);
//   assert (a.fieldModes == a.fieldModes);
//
//
// assert m.boundsNestingOK(a, m.oHeap);
// m.boundsNestingWiderContext(a, m.oHeap, m.oHeap+m.ns+{a});
//
// assert m.boundsNestingOK(a, m.oHeap+m.ns+{a});
//
// assert a.allExternalOwners() <= m.m.Keys ;
// assert a.allExternalBounds() <= m.m.Keys ;
// InTheBox(a,m);
// assert m.boundsNestingOK(a, m.m.Keys+{a});
//
//   //this is cloneOUTSIDE -= so a == b?  riugbht??
//
//   // && m.boundsNestingOK(b, m.oHeap+m.ns)
//   // && m.boundsNestingOK(a, m.m.Keys+{a})
//   // && m.fieldMappingsOK(a, b, m.m.Keys+{a});
//
// }  ///end KlonKV
//
// {
//   reveal m.calidSheep();
//   assert m.calidSheep();
//   reveal m.AreWeNotMen();
//   assert forall k <- m.m.Keys :: m.AreWeNotMen(k,m);
//   assert m.AreWeNotMen(a, klonKV(m,a,a));
//
//     ///////////////////////////////////////////////////////////////
//   m := m.putOutside(a);   ///HOPEY?  CHANGEY?
//     print "done? rashy?  washy?\n";
//   ///////////////////////////////////////////////////////////////
//
//
// }
//
//   assert b.fieldModes == a.fieldModes;
//   assert (b == a) by {
//     assert not(inside(a, m.o));   //glurk
//     assert m.AreWeNotMen(a,m);
//     assert b == a;      //double glurk
//   }
//
//
//
//     assert m.m[a] == b;
//
//     assert  m.o     == m0.o;
//     assert  m.oHeap == m0.oHeap;
//     assert  m.ns    >= m0.ns;
//
//     assert m.calid();
//     reveal m.calid();
//     assert m.calidObjects();
//     assert m.calidOK();
//     reveal m.calidSheep();
//     assert m.calidSheep();
//
//     assert a in m.m.Keys;
//     assert b.fieldModes == a.fieldModes;
//
// print "returnin' from the outsidee case\n";
//
//     // assert a !in m0.m.Keys ==> b !in m0.ns;   //KJX sure about this?
//
//     return;  //we may as well just return here.
//              //we've done all we need to do.  I think.
//
//   }///END OF THE OUTSIDE CASE
//   else
//   { //start of the Inside case
// print "start of the Inside case\n";
//       print "Clone_Via_Map owners:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
//
//   ///////////////////////////////////////////////////////////////
//       b, m := Clone_Clone_Clone(a, m);
//   ///////////////////////////////////////////////////////////////
//
//       // assert a !in m0.m.Keys ==> b !in m0.ns;  }  //end of inside case
//
//
// print "end of the Inside case\n";
//
//   } //end of inside case
//
//   ///////////////////////////////////////////////////////////////
//   //tidying up after the cases..
//
//   // assert a !in m0.m.Keys ==> b !in m0.ns;   //KJX sure about this?
//
//   reveal m.calid();
//   assert m.calid();
//   reveal m.calidObjects();
//   assert m.calidObjects();
//   reveal m.calidOK();
//   assert m.calidOK();
//   assert CallOK(m.m.Values, m.oHeap+m.ns);
//   assert b in m.m.Values;
//   assert b in m.m.Values;
//   COKfromCallOK(b, m.m.Values, m.oHeap+m.ns);
//   assert COK(b, m.oHeap+m.ns);
//   assert BOK: COK(b, m.oHeap+m.ns);
//   //  assert fresh(b);   //umm, yeah should probalboy be fresh at least if INSIDE, but...
//   //  have to experiment with a clause somewhere in calidSheep saying every inside clone is new
//   //  or everyhing in ns2 is new. or...
//   //   assert b in m.ns;
//
//   assert m.m[a] == b;
//   assert a !in m0.m.Keys;
//   // assert b !in m0.oHeap;   //need to decided whet)her this is (nominally) both iunsier or outside, or just inside
//   //assert b !in m0.ns;;
//
//
//   //  assert  b.fields.Keys == {};
//
//   assert  b.fieldModes.Keys == a.fieldModes.Keys;
//
//   reveal m.calidSheep();
//   assert m.calidSheep();
//
//   assert  b.fieldModes == a.fieldModes;
//
//   //  assert a !in m0.m.Keys ==> b !in m0.ns;   //KJX sure about this?
//
//   //  assert m.from(m0) by {
//   //      reveal m.from();
//   assert  m.o     == m0.o;
//   assert  m.oHeap == m0.oHeap;
//   assert  m.ns    >= m0.ns;
//
//   assert COK(b, m.oHeap+m.ns) by { reveal BOK; }
//
//   assert m.from(m0);
//   //  }
//   print "RETN Clone_Via_Map:", fmtobj(a), " pivot:", fmtobj(m.o), "\n";
//
// }


//
// method PLACEHOLDER_Clone_All_Fields(a : Object, b : Object, m0 : Klon)
//   returns (m : Klon)
//   //clone all fields a.n into b.n
//   //a should be preexisting (in m0.oHeapl); b should be "new"  in m0.ns
//
//   decreases (m0.oHeap - m0.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10 //Clone_All_Fields
//
//   requires MPRIME: m0.calid()
//   requires COK(a, m0.oHeap)
//   requires COK(b, m0.oHeap+m0.ns)
//
//   requires b.fields.Keys == {}
//
//   requires a.fields.Keys <= a.fieldModes.Keys
//   requires a.fieldModes == b.fieldModes
//
//
//   requires a in m0.oHeap
//   requires a in m0.m.Keys
//
//   requires b in m0.m.Values
//   requires b in m0.ns
//   requires (a in m0.m.Keys) && m0.m[a] == b
//   requires m0.o    in m0.oHeap
//   requires m0.m.Keys   <= m0.oHeap
//
//   requires a.AMFO <= m0.m.Keys  //seems weird but we are populating m, right...
// //  requires b.AMFO == mapThruKlon(a.AMFO, m0)  //KJXFRIDAY13TH
// //  requires b.AMFO <= m0.m.Values
//   requires b.AMFO <= m0.oHeap+m0.ns
//
//   // requires b.fieldModes[n] == Evil //evilKJX this is actually evil
//   //well not *that* evil as I still must satisfy refOK
//   //
//   // requires forall n <- b.fields :: (n in b.fieldModes) &&
//   //             AssignmentCompatible(b, b.fieldModes[n], b.fields[n])
//
//   //consequently
//   //   requires refOK(a, a.fields[n])
//
//   ensures  m.calid()
//   ensures  old(m0.calid())
//   ensures  klonVMapOK(m.m)
//   ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//
//   //ensures  b.fields.Keys == a.fields.Keys  //FUCK
//   ensures a.fieldModes == b.fieldModes
//
//   ensures  a in m.m.Keys
//   ensures  (a in m.m.Keys) && m.m[a] == b
//
//
//
//   //   ensures  n in b.fields
//   //   ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]
//
//   ensures  b in m.m.Values
//
//   ensures  mapLEQ(m0.m,m.m)
//
//   ensures  CallOK(m.oHeap)
//   ensures  COK(a, m.oHeap)
//   ensures  COK(b, m.oHeap+m.ns)
//   ensures  CallOK(m.m.Values, m.oHeap+m.ns)
//   ensures  CallOK(m.ns, m.oHeap+m.ns)
//
//   ensures  m.o     == m0.o
//   ensures  m.oHeap == m0.oHeap
//   ensures  m.ns    >= m0.ns
//   ensures  m.m.Keys    <= m.oHeap
//
//
//   ensures  unchanged(a)
//   ensures  unchanged(m0.oHeap)
//   ensures  unchanged(m0.ns - {b})  //will this work?
//
//   ensures  forall x <- (m.m.Values - {b}) :: old(allocated( x )) ==> unchanged( x ) //duesb;t veruft....
//
//   //  modifies (set o : Object | o !in m0.oHeap)`fields
//   // modifies (set o : Object | o !in ((m0.oHeap+m0.ns) - {b}))`fields
//   //or can this  be modifies m0.ns?
//   modifies b`fields   ///GGRRR
// {
//   m := m0;
//
// // assert b.AMFO == mapThruKlon(a.AMFO, m0);
// assert b in m0.m.Values;
// assert m0.m[a] == b;  //mmmKJX
//
// //TUESDAY15DEC2024
//
// assert b.AMFO <= (m0.oHeap+m0.ns)
// by
//    {
//       assert COK(b,m0.oHeap+m0.ns);
//       reveal COK();
//    }
//
// // assert (b.AMFO <= m0.m.Values) by {
// //   assert m0.calid() by { reveal MPRIME; }
// //   reveal m0.calid(), m0.calidMap();
// //   assert m0.calidMap();
// //   assert (forall x <- m0.m.Keys ::
// //         && m0.boundsNestingOK(m0.m[x], m0.oHeap+m0.ns));
// //
// //   assert a in m0.m.Keys;
// //   assert b in m0.m.Values;
// // `  assert COK(b,m0.oHeap+m0.ns);`
// //   assert m0.boundsNestingOK(b, m0.oHeap+m0.ns);
// //   assert ownerInsideOwnerInsideOwner(m0.oHeap+m0.ns, b.AMFO, b.AMFB);
// // }
//
//   print "CALL Clone_All_Fields: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";
//
//
//   assert m0.calid() by { reveal MPRIME; }
//
//   assert BINNS:  b in m.ns;
//   print "VARIANT CAF ", |(m0.oHeap - m0.m.Keys +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";
//   print "<<<<<<<<<<<\n";
//   print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
//   print "<<<<<<<<<<<\n";
//
//
//   assert unchanged(a) && unchanged(m.oHeap);
//
//   assert  m.o == m0.o;
//   assert  m.oHeap == m0.oHeap;
//   assert  m.ns == m0.ns;
//   assert  m.m.Values == m0.m.Values;
//
//   assert  m.m.Keys == m0.m.Keys;
//   assert  a in m0.m.Keys;
//
//   assert m.m[a] == b;  //mmmKJX
//   // assert (a in m.m.Keys) ==> (m[a] == b);  //mmmKJX
//
//   assert m.calid();
//   assert m0.calid() by { reveal MPRIME; }
//   assert COK(b, m.oHeap+m.ns);
//   assert HEREB: COK(b, m.oHeap+m.ns);
//
//
//
//
//   //assert fresh(b);
//   assert  b.fields.Keys == {};
//   assert b in m.m.Values;
//
//   //START OF FIELDS…
//
//   print "<<<<<<<<<<<\n";
//   printmapping(m.m);
//   print "<<<<<<<<<<<\n";
//
//   assert m.calid();
//   assert m0.calid() by { reveal MPRIME; }
//
//   var fieldNames : seq<string> := set2seq(a.fields.Keys);
//
//   assert forall k <- a.fields.Keys :: (multiset(a.fields.Keys))[k] == 1;
//   assert forall s <- fieldNames :: (multiset(fieldNames))[s] == 1;
//   assert forall i | 0 <= i < |fieldNames|, j | 0 <= j < |fieldNames| :: (fieldNames[i] == fieldNames[j]) <==> i == j;
//   //assert b.fields.Keys == {};
//   assert b.fields.Keys == seq2set(fieldNames[..0]);
//
//
//   print "Clone_All_Fields fields:", fmtobj(a), " fields=", fmtseqstr(fieldNames), "\n";
//
//   //DOING FIELDS≈≈
//
//   print "BLOOP BLOOP BLOOP\n";
//
//   assert m.calidOK() by {
//     assert m.calid();
//     reveal m.calid();
//     assert m.calidOK();
//   }
//
//   assert COK(b, m.oHeap+m.ns);
//
//   assert m0.calid() by { reveal MPRIME; }
//
//   label BLOOP:
//
//   assert m.calidOK();
//   reveal m.calidOK();
//   assert m.calid();
//   assert CallOK(m.ns, m.oHeap+m.ns);
//   assert CallOK(m.m.Values, m.oHeap+m.ns);
//
//   assert CallOK(m.m.Keys, m.oHeap) by {}
//
//
//
//   var rm := m;
//
//   assert  rm.o     == m.o      == m0.o;
//   assert  rm.oHeap == m.oHeap  == m0.oHeap;
//   assert  rm.ns    >= m.ns     >= m0.ns;
//   assert  rm.m.Values    >= m.m.Values     >= m0.m.Values;
//   assert  m.m.Keys     <= rm.m.Keys    <= m.oHeap;
//
//
//   COKgetsDeclaredFields(a, m.oHeap);
//   assert unchanged(a) && unchanged(m.oHeap);
//   assert CallOK(m.m.Keys, m.oHeap);
//
//   assert b.fields.Keys == seq2set(fieldNames[..0]) == {};
//
//   for i := 0 to |fieldNames|
//
//     invariant  rm.o     == m.o      == m0.o
//     invariant  rm.oHeap == m.oHeap  == m0.oHeap
//     invariant  rm.ns    >= m.ns     >= m0.ns
//     invariant  rm.m.Values    >= m.m.Values     >= m0.m.Values
//     invariant   m.m.Keys    <= rm.m.Keys    <= m.oHeap
//
//     invariant  b in m.ns
//     invariant  b in m.m.Values
//
//     invariant COK(a, m.oHeap)
//     invariant COK(b, m.oHeap+m.ns)
//     invariant mapLEQ(m0.m,m.m)
//     invariant a in m.oHeap
//     invariant a in m.m.Keys
//     invariant m.o in m.oHeap
//     invariant CallOK(m.oHeap)
//     invariant CallOK(m.m.Keys, m.oHeap)
//     invariant CallOK(m.ns, m.oHeap+m.ns)
//     invariant CallOK(m.m.Values, m.oHeap+m.ns)
//     invariant m.calid()
//     invariant old(m0.calid())
//
//     invariant unchanged(a)
//     invariant unchanged(m.oHeap)
//     //invariant forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.at(x) == x))
//     invariant (m0.oHeap - m0.m.Keys +{a}) >= (m.oHeap - m.m.Keys +{a})
//     invariant (m0.oHeap - m0.m.Keys) >= (m.oHeap - m.m.Keys)
//     invariant b.fields.Keys == seq2set(fieldNames[..i])
//     invariant forall i | 0 <= i < |fieldNames|, j | 0 <= j < |fieldNames| :: (fieldNames[i] == fieldNames[j]) <==> i == j
//
//     invariant  m.m[a] == b
//     invariant  a.fieldModes == b.fieldModes
//     invariant  a.AllFieldsAreDeclared()
//
//
//     invariant old(m0.calid())
//   {
//     assert b.fields.Keys == seq2set(fieldNames[..i]);
//
//     assert COK(b, m.oHeap+m.ns);
//
//     var n : string := fieldNames[i];
//     var ofv : Object := a.fields[n];
//
//     assert n !in seq2set(fieldNames[..i]);
//
//     assert (n !in b.fields.Keys) by {
//       assert n !in seq2set(fieldNames[..i]);
//       assert b.fields.Keys == seq2set(fieldNames[..i]);
//       assert (n !in b.fields.Keys);
//     }
//
//     print "  TLOOP  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
//     print "  TLOOP  (recurse on field ",n,")\n";
//     print "  TLOOP m:", |m.oHeap - m.m.Keys|, " m0:", |m0.oHeap - m0.m.Keys|, "\n";
//     print "  TLOOP b.fieldsKeys==", b.fields.Keys, "\n";
//     print "  TINV                ", fieldNames[..i], "\n";
//     print "  TLOOPINV            ",seq2set(fieldNames[..i]),"\n";
//
//
//     print "VARIANT*CAF ", |(m0.oHeap - m0.m.Keys +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";
//
//
//     //   assert (m.oHeap - m.m.Keys) < (m0.oHeap - m0.m.Keys);
//
//     assert  rm.o     == m.o      == m0.o;
//     assert  rm.oHeap == m.oHeap  == m0.oHeap;
//     assert  rm.ns    >= m.ns     >= m0.ns;
//     assert  rm.m.Keys    >= m.m.Keys     >= m0.m.Keys;
//     assert  rm.m.Values    >= m.m.Values     >= m0.m.Values;
//     assert  m.m.Keys     <= rm.m.Keys    <= m.oHeap;
//
//     assert b in m.ns by { reveal BINNS; assert b in m.ns; }
//     assert n !in b.fields;
//     assert refOK(a, a.fields[n])
//     by {
//       assert m.calid();  reveal m.calid();
//       assert m.calidOK(); reveal m.calidOK();
//       assert COK(a,m.oHeap); reveal COK();
//       assert a.AllOutgoingReferencesAreOwnership(m.oHeap);
//       assert  refOK(a, a.fields[n]);
//       // - inside(f,t.owner);
//     }
//
//     assert a.AllFieldsAreDeclared();
//     assert a.fields.Keys <= a.fieldModes.Keys;
//     assert a.fieldModes == b.fieldModes;
//     assert n in b.fieldModes;
//
//
//     assert forall n <- b.fields ::
//         && (n in b.fieldModes)
//         && AssignmentCompatible(b, b.fieldModes[n], b.fields[n])
//     by {
//       assert m.calid();
//       reveal m.calid();
//
//       assert old(m0.calid());
//
//       assert COK(b, m.oHeap+m.ns);
//       reveal COK();
//       assert b.Valid();
//       assert b.AllFieldsContentsConsistentWithTheirDeclaration();
//       assert forall n <- b.fields ::
//           AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
//     }
//
//     var OLDFLDS := b.fields.Keys;
//
//     assert b in m.ns;
//     assert b in m.m.Values;
//     assert a in m.m.Keys;
//
//
//
//     var v_caf := ((m0.oHeap - m0.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10);
//     var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map
//
//     print "v_caf ", v_caf, "\n";
//     print "v_cfm ", v_cfm, "\n";
//
//     assert b.fields.Keys == seq2set(fieldNames[..i]);
//     assert a.fields.Keys == seq2set(fieldNames);
//
//     print "okaoka ", (m0.oHeap - m0.m.Keys +{a}) >  (m.oHeap - m.m.Keys +{a}), "\n";
//     print "okaoka ", (m0.oHeap - m0.m.Keys +{a}) == (m.oHeap - m.m.Keys +{a}), "\n";
//
//     assert (m0.oHeap - m0.m.Keys +{a}) >= (m.oHeap - m.m.Keys +{a});
//     assert a.AMFO >= a.AMFO;
//     assert (a.fields.Keys) >= (a.fields.Keys - b.fields.Keys);
//     assert 10 > 5;
//
//     label B4CLONEFIELD:
//
//     assert  old(m0.calid());
//
// //////////////////////////////////////////////////////
// //preconditions for Clone_Field_Map(a,n,b,m);
// //////////////////////////////////////////////////////
//
//   assert m.calid();
//   assert COK(a, m.oHeap);
//   assert COK(b, m.oHeap+m.ns);
//
//   assert n  in a.fields.Keys;
//   assert n !in b.fields.Keys;
//
//   assert n  in a.fieldModes;
//   assert n  in b.fieldModes;
//   assert a.fieldModes == b.fieldModes;
//   assert FLDMODZ: a.fieldModes == b.fieldModes;
//   assert a in m.oHeap;
//   assert a in m.m.Keys;
//   assert a.AMFO <= m.m.Keys;
//   assert b in m.ns;
//   assert b in m.m.Values;
// //  assert b.AMFO <= m.m.Values;
//   assert b  in m.oHeap+m.ns; //TUESDAY17DEC2024
//   assert (a in m.m.Keys) && m.m[a] == b;
//   assert m.o    in m.oHeap;
//   assert m.m.Keys   <= m.oHeap;
//   assert forall n <- b.fields :: (n in b.fieldModes) && AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
//   assert refOK(a, a.fields[n]);
//
//
//
//
//   assert m.calid();
//   assert COK(a, m.oHeap);
//   assert COK(b, m.oHeap+m.ns);
//
//   assert n  in a.fields.Keys;
//   assert n !in b.fields.Keys;
//
//   assert n  in a.fieldModes;
//   assert n  in b.fieldModes;
//   assert a.fieldModes == b.fieldModes;
//   assert a.fieldModes == b.fieldModes;
//   assert a in m.oHeap;
//   assert a in m.m.Keys;
//   assert a.AMFO <= m.m.Keys; //KJX should be part of some invariant;
//   assert b in m.ns;
//   assert b in m.m.Values;
//   assert b.AMFO <= m.oHeap+m.ns  ;
//   assert (a in m.m.Keys) && m.m[a] == b;
//   assert m.o    in m.oHeap;
//   assert m.m.Keys   <= m.oHeap;
//   assert forall n <- b.fields :: (n in b.fieldModes) && AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
//   assert refOK(a, a.fields[n]);
//
//
// //////////////////////////////////////////////////////
// //////////////////////////////////////////////////////
//
//
//     rm := Clone_Field_Map(a,n,b,m);
//
//
// //////////////////////////////////////////////////////
// //////////////////////////////////////////////////////
//
//     assert  old(m0.calid());
//
//     assert  rm.o     == m.o      == m0.o;
//     assert  rm.oHeap == m.oHeap  == m0.oHeap;
//     assert  rm.ns    >= m.ns     >= m0.ns;
//     assert  rm.m.Keys    >= m.m.Keys     >= m0.m.Keys;
//     assert  rm.m.Values    >= m.m.Values     >= m0.m.Values;
//     assert  m.m.Keys     <= rm.m.Keys    <= m.oHeap;
//
//     //   assert old@B4CLONEFIELD(forall x <- m0.m.Keys :: x.fieldModes == m0.m[x].fieldModes);
//     //   assert (forall x <- m0.m.Keys :: x.fieldModes == old@B4CLONEFIELD(x.fieldModes));
//     //   assert (forall x <- m0.m.Keys :: m0.m[x].fieldModes == old@B4CLONEFIELD(m0.m[x].fieldModes));
//     //   assert (forall x <- m0.m.Keys :: x.fieldModes == m0.m[x].fieldModes);
//     //
//
//     assert n == fieldNames[i];
//     assert n in b.fields.Keys;
//     assert b.fields.Keys == OLDFLDS + {n};
//
//
//     nqf(n,fieldNames[i]);
//
//     assert {n} == {fieldNames[i]} == seq2set([ n ]) == seq2set([ fieldNames[i] ]);
//     assert {n} == {fieldNames[i]} == seq2set([ fieldNames[i] ]);
//
// //    invariant  b.fields.Keys == seq2set(fieldNames[..i])
//
//     extendSeqSet(fieldNames, i);
//
//   assert  seq2set(fieldNames[..i+1]) == seq2set(fieldNames[..i]) + seq2set([fieldNames[i]]);
//
//   assert  seq2set(fieldNames[..i+1]) == seq2set(fieldNames[..i]) + seq2set([n]);
//
//   assert b.fields.Keys == seq2set(fieldNames[..i+1]);
//
//
// //    assert b.fields.Keys == seq2set(fieldNames[..i]) + seq2set([fieldNames[i]]);
//
// //    assert b.fields.Keys == seq2set(fieldNames[..(i+1)]);
//
//     // assert fieldNames[..i] + [fieldNames[i]] == fieldNames[..i+1];
//     // assert b.fields.Keys == seq2set(fieldNames[..i]) + seq2set([fieldNames[i]]);
//     // assert b.fields.Keys == seq2set(fieldNames[..i+1]);
//
//     assert rm.from(m);
//     //assert m.from(m0);
//     //assert rm.from(m0);
//
//
//     assert rm.calid();
//     //  assert COK(b, m.oHeap+m.ns );
//     m := rm;
//     assert m.calid();
//     assert old(m0.calid());
//
//     //  by {
//     //    reveal MPRIME; reveal m.calid();
//     //
//     //    assert m0 == m0;
//     //    assert mapLEQ(m0.m, m.m);
//     //
//     //    assert forall k <- m0.m.Keys :: m0.m[k] == m.m[k];
//     //    assert forall k <- m0.m.Keys :: m0.m[k].fields == m.m[k].fields;
//     //    assert forall k <- m0.m.Keys :: m0.m[k] == m.m[k];
//     //    assert forall k <- m0.m.Keys :: m0.m[k].fields == m.m[k].fields;
//     //
//     //             reveal m0.calid();
//     // //            assert m0.calid();
//     //
//     //         assert (m0.o in  m0.oHeap);
//     //         assert (m0.m.Keys <= m0.oHeap);
//     //         assert (m0.m.Values <= m0.oHeap+m0.ns);
//     //         assert COK(m0.o, m0.oHeap);
//     //         assert CallOK(m0.oHeap);
//     //         assert CallOK(m0.m.Keys, m0.oHeap);
//     //
//     //         assert CallOK(m0.m.Values-{b}, m0.oHeap+m0.ns) by
//     //           {
//     //
//     //           }
//     //
//     //         assert CallOK(m0.ns-{b}, m0.oHeap+m0.ns) by
//     //           {
//     //
//     //           }
//     //
//     //         // assert CallOK(m0.m.Values, m0.oHeap+m0.ns);
//     //         // assert CallOK(m0.ns, m0.oHeap+m0.ns);
//     //
//     //             reveal m0.calidOK();
//     //             assert m0.calidOK();
//     //             reveal m0.calidObjects();
//     //             // assert m0.calidObjects();
//     //             reveal m0.calidMap();
//     //             // assert m0.calidMap();
//     //             assert m0.m.Keys == m0.m.Keys;
//     //
//     //         reveal m0.AreWeNotMen();
//     //         //reveal UniqueMapEntry();
//     //
//     //         assert (forall x <- m0.m.Keys :: m0.AreWeNotMen(x, m0));
//     //         assert (forall x <- m0.m.Keys :: x.fieldModes == m0.m[x].fieldModes);
//     //         assert AllMapEntriesAreUnique(m0.m);
//     //
//     //             reveal m0.calidSheep();
//     //             assert m0.calidSheep();
//     //
//     //    assert m0.calid(); }
//     //
//
//
//     assert  CallOK(m.m.Keys, m.oHeap)
//     by { reveal m.calid();    assert m.calid();
//          reveal m.calidOK();  assert m.calidOK();
//        }
//   } //end of loop
//
//   assert unchanged(a) && unchanged(m.oHeap);
//
//
//   //DONE FIELDS
//
//   assert COK(b, m.oHeap+m.ns) by { reveal HEREB; }
//   assert mapLEQ(m0.m,m.m);
//   //
//   // assert m0.calid() by { reveal MPRIME; }
//
//   reveal m.calid();
//   assert m.calid();
//   reveal m.calidObjects();
//   assert m.calidObjects();
//
//   reveal m.calidMap(); assert m.calidMap();
//   reveal m.calidSheep(); assert m.calidSheep();
//
//
//   assert m.m[a] == b;
//
//   assert m.at(a) == b;
//   assert a in m.m.Keys;
//   assert b in m.oHeap+m.ns;
//
//   assert COK(b, m.oHeap+m.ns);
//
//   assert mapLEQ(m0.m,m.m);
//
//
//   assert CallOK(m.oHeap);
//   assert COK(a, m.oHeap);
//   assert COK(b, m.oHeap + m.ns);
//   assert CallOK(m.m.Values, m.oHeap+m.ns);
//   assert COK(b, m.oHeap  + m.ns);
//
//
//   reveal m.calidObjects(); assert m.calidObjects();
//
//
//   assert COK(m.o, m.oHeap);
//   assert CallOK(m.oHeap);
//   assert CallOK(m.m.Keys, m.oHeap);
//   assert CallOK(m.m.Values, m.oHeap+m.ns);
//   assert CallOK(m.ns, m.oHeap+m.ns);
//
//   reveal m.calidOK(); assert m.calidOK();
//
//   reveal m.calidMap(); assert m.calidMap();
//
//   assert klonVMapOK(m.m);
//
//
//
//   assert  rm.o     == m.o      == m0.o;
//   assert  rm.oHeap == m.oHeap  == m0.oHeap;
//   assert  rm.ns    >= m.ns     >= m0.ns;
//   assert  rm.m.Values    >= m.m.Values     >= m0.m.Values;
//
//   reveal m.calidObjects(); assert m.calidObjects();
//   reveal m.calidOK(); assert m.calidOK();
//   reveal m.calidSheep(); assert m.calidSheep();
//
//   assert m.m.Keys == m.m.Keys;
//
//   reveal m.AreWeNotMen();
//   assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
//   assert forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.m[x] == x));
//
//   assert  b.fieldModes == a.fieldModes;
//
//   reveal m.calid(); assert m.calid();
//
//   // assert m0.calid() by { reveal MPRIME; }
//
//   assert klonVMapOK(m.m) && a.AMFO <= m.m.Keys;
//   assert unchanged(a) && unchanged(m.oHeap);
//   //
//   //     assert m0.calid() by {
//   //        assert unchanged(m0.m.Keys);
//   //        assert unchanged(m0.m.Values - {b});
//   //        //assuage COK(b, m.oHeap + m.ns);
//   //        //assuage m0.m.Values - {b} + {b} == m0.m.Values;
//   // //       assert
//   //        assert CallOK(m0.m.Values, m.oHeap + m.ns);
//   //
//   //         assert m0.calidObjects();
//   //         assert m0.calidOK();
//   //         assert m0.calidMap();
//   //         assert m0.calidSheep();
//   //
//   //
//   assert old(m0.calid());
//   //     }
//   print "RETN Clone_All_Fields done ", fmtobj(a), "\n";
//
//   return;
// }
// //end PLACEHOLDER_Clone_All_Fields
//



// method Clone_Outside_Heap(a : Object, m0 : Klon)
//   returns (b : Object, m : Klon)
//   decreases (m0.oHeap - m0.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Outside_Heap

//   //extraOK  requires a.extra == {} //extra not yet cloned

//   //this case
//   requires a !in m0.m.Keys
//   requires a !in m0.m.Values
//   requires outside(a,m0.o)

//   //all Clone_
//   requires m0.calid()
//   requires a in m0.oHeap
//   requires COK(a, m0.oHeap) //bonus - covered in the above :-)

//   ensures  m.calid()
//   ensures  a == b
//   ensures  a in m.m.Keys
//   ensures  a in m.m.Keys
//   ensures  b in m.m.Values
//   ensures  b in m.m.Values
//   ensures  a in m.m.Keys && m.at(a) == b
//   ensures  COK(b, m.oHeap+m.ns)

//   //should I package this up - as aw twostate or a onestate?
//   ensures  mapLEQ(m0.m,m.m)
//   ensures  m.m.Keys >= m0.m.Keys + {a}
//   ensures  m.m.Values >= m0.m.Values + {b}
//   ensures  m.o == m0.o
//   ensures  m.oHeap == m0.oHeap
//   ensures  m.ns >= m0.ns
//   //  ensures  if (inside(a, m0.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//                           //this means that on return, every owner is now in the map...
//   ensures m.from(m0)

//   //ensures b.AMFO == set x <- a.AMFO :: m.m[x]

//   ensures b.fieldModes == a.fieldModes
//   //  ensures b.fields.Keys == a.fields.Keys

//   //  modifies (set o : Object | o !in (m0.oHeap+m0.ns))`fields
//   // ensures  a !in m0.m.Keys ==> b !in m0.ns  //KJX sure about this?
//   modifies {}
// {
//   m := m0;

//   assert m.m.Keys == m0.m.Keys;
//   assert a !in m.m.Keys;
//   assert a !in m.m.Values;

//   assert m == m0;
//   assert m.m == m0.m;
//   assert mapLEQ(m0.m,m.m);
//   assert m.from(m0);

//   print "Clone_Outside_Heap outside owners:", fmtobj(a), " owned by ", fmtobj(a.owner) ,"\n";
//   print "VARIANT COH ", |(m0.oHeap - m0.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

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
//   assert rm.from(m0);
//   assert klonVMapOK(rm.m);
//   reveal rm.calid(); assert rm.calid();
//   reveal rm.calidObjects(); assert rm.calidObjects();
//   assert rm.m.Keys == rm.m.Keys;
//   reveal rm.calidMap(); assert  rm.calidMap();
//   assert (forall x <- rm.m.Keys, oo <- x.AMFO :: rm.m[oo] in rm.m[x].AMFO);
//   assert (forall x <- rm.m.Keys,     oo <- x.AMFO :: rm.m[oo] in rm.m[x].AMFO);
//   assert rm.m.Keys >= m0.m.Keys;
//   assert mapLEQ(m0.m,rm.m);
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
//     assert m.from(m0);
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
//   assert rm.m.Keys >= m0.m.Keys;
//   assert mapLEQ(m0.m,rm.m);
//   assert rm.from(m0);

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
//   assert xm.m.Keys >= m0.m.Keys;
//   assert mapLEQ(m0.m,xm.m);
//   assert xm.from(rm);
//   assert xm.from(m0);

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
//   assert xm.m.Keys >= (m0.m.Keys);
//   assert mapLEQ(m0.m,xm.m);
//   assert xm.from(m0);

//   assert a !in xm.m.Keys;

//   while ((MX != {}) && (a !in xm.m.Keys))
//     decreases MX
//     invariant MX == a.owner - xm.m.Keys
//     invariant MX <= a.allExternalOwners()
//     invariant xm == rm
//     invariant xm.calid()
//     invariant rm.calid()
//     invariant old(m0.calid())
//     invariant xm.from(m0)
//     invariant MX <= xm.oHeap
//     invariant CallOK(xm.oHeap)
//     invariant a.AMFO - {a} <= xm.m.Keys + MX
//     invariant oldmok ==> assigned(oldmks)
//     invariant oldmok ==> (xm.m.Keys > oldmks)
//     invariant m0.oHeap == xm.oHeap
//     invariant oldmok ==> ((m0.oHeap - oldmks) > (xm.oHeap - xm.m.Keys))
//     invariant xm.m.Keys >= (m0.m.Keys)
//     invariant xm.m.Values >= (m0.m.Values)
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


//     assert oldmok ==> (m0.oHeap - oldmks) > (xm.oHeap - xm.m.Keys);

//     assert xo in a.AMFO;
//     assert a.Ready();
//     assert a.AMFO > xo.AMFO;


//     assert (m0.oHeap) == m0.oHeap == xm.oHeap;
//     assert xm.m.Keys >= (m0.m.Keys);
//     assert xm.from(m0);

//     assert  mapLEQ(m0.m,xm.m) by
//     { reveal xm.calid(); assert xm.calid();
//       reveal xm.calidObjects(); assert xm.calidObjects();
//       assert m0.m.Keys <= xm.m.Keys;
//       assert m0.m.Values <= xm.m.Values;
//       assert m0.m.Keys == m0.m.Keys;
//       assert m0.m.Values == m0.m.Values;
//       assert xm.m.Keys == xm.m.Keys;
//       assert xm.m.Values == xm.m.Values;
//       assert m0.m.Keys <= xm.m.Keys;
//       assert m0.m.Values <= xm.m.Values;
//       assert forall k <- m0.m.Keys :: k in xm.m.Keys;
//       assert forall k <- m0.m.Keys :: k in xm.m.Keys && (m0.m[k] == xm.m[k]);
//     }

//     //
//     //                   assert xm.m.Keys >= m0.m.Keys;
//     //                 assert a !in xm.m.Keys;
//     //
//     //           assert ((m0.oHeap - m0.m.Keys)) >= (xm.oHeap - xm.m.Keys);
//     //
//     // assert  ((a.AMFO)
//     //   decreases to
//     //         (xo.AMFO));
//     //
//     //         assert ((m0.oHeap - m0.m.Keys),
//     //                (a.AMFO),
//     //                (a.fields.Keys),
//     //                (15)
//     //           decreases to
//     //                xm.oHeap - xm.m.Keys,
//     //                xo.AMFO,
//     //                xo.fields.Keys,
//     //                20);


//     rr, rm := Clone_Via_Map(xo, xm);
//     assert rm.m.Keys >= m0.m.Keys;
//     assert mapLEQ(m0.m,rm.m);
//     assert rm.from(m0);

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

//       assert m.from(m0);

//       assert  mapLEQ(m0.m,m.m) by
//       { reveal m.calidObjects(); assert m.calidObjects();
//         assert m0.m.Keys <= m.m.Keys;
//         assert mapLEQ(m0.m,m.m);
//         assert m0.m.Keys <= m.m.Keys;
//         assert m0.m.Values <= m.m.Values;
//       }
//       assert  m.m.Keys >= m0.m.Keys + {a} by { reveal m.calidObjects(); assert m.calidObjects(); }
//       assert  m.m.Values >= m0.m.Values + {b} by { reveal m.calidObjects(); assert m.calidObjects(); }
//       assert  m.o == m0.o;
//       assert  m.oHeap == m0.oHeap;
//       assert  m.ns >= m0.ns;
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
//     assert xm.m.Keys >= m0.m.Keys;
//     assert xm.m.Keys > oldmks;

//     assert xm.from(m0);


//     //          MX := a.extra - rm.m.Keys;
//     assert xm == rm;
//   } // end loop MX


//   assert xm == rm;
//   assert xm.m.Keys >= m0.m.Keys;
//   assert a !in xm.m.Keys;
//   assert (a.AMFO - {a})<= xm.m.Keys;


//   assert xm.calid(); assert rm.calid();
//   assert a.AMFO - {a} <= rm.m.Keys;
//   //  SubsetOfKeysOfExtendedMap(a.AMFO , rm, m);
//   assert a.allExternalOwners() ==  a.AMFO - {a};
//   assert a.AMFO == flattenAMFOs(a.owner) + {a};
//   assert a.allExternalOwners() <= rm.m.Keys;
//   assert xm.m.Keys >= m0.m.Keys;
//   assert xm.from(m0);
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
//   assert m.from(rm);  assert m.from(m0);
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



// method Clone_Outside_World(a : Object, m0 : Klon)
//   returns (b : Object, m : Klon)
//   decreases (m0.oHeap - m0.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Outside_World

//   //extraOK  requires a.extra == {} //extra not yet cloned

//   //this case
//   requires a !in m0.m.Keys
//   requires a !in m0.m.Values
//   requires outside(a,m0.o)

//   //all Clone_
//   requires m0.calid()
//   requires a in m0.oHeap
//   requires COK(a, m0.oHeap)


//   ensures  m.calid()
//   ensures  a in m.m.Keys
//   ensures  a in m.m.Keys
//   ensures  b in m.m.Values
//   ensures  b in m.m.Values
//   ensures  a in m.m.Keys && m.at(a) == b
//   ensures  COK(b, m.oHeap+m.ns)

//   //should I package this up - as aw twostate or a onestate?
//   ensures  mapLEQ(m0.m,m.m)
//   ensures  m.m.Keys >= m0.m.Keys + {a}
//   ensures  m.m.Values >= m0.m.Values + {b}
//   ensures  m.o == m0.o
//   ensures  m.oHeap == m0.oHeap
//   ensures  m.ns >= m0.ns
//   //  ensures  if (inside(a, m0.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//   ensures m.from(m0)

//   //ensures b.AMFO == set x <- a.AMFO :: m.m[x]

//   ensures a.fieldModes == b.fieldModes
//   // ensures b.fields.Keys == a.fields.Keys
//   // modifies (set o : Object | o !in (m0.oHeap+m0.ns))`fields
//   // ensures  a !in m0.m.Keys ==> b !in m0.ns  //KJX sure about this?
//   modifies {}
// {
//   m := m0;


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
//   print "VARIANT COW ", |(m0.oHeap - m0.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";
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


// method Clone_KaTHUMP(a : Object, m0 : Klon)
//   //spike method to test AMFO being "owner-closed"
//   //means the clones are "owner-cooned"
//   // that all the owners (and their AMFOS) are in the current objects AMFOS
//   //  i.e,  forall oo <- MYOWNERS :: oo in oo.AMFO
//   //  forall oo <- MYOWNERS - this? :: oo.AMFO <= this.AMFO..
//   // so if .e.g a[x] == c,   then we want m[a[x]] == m[c]...
//   // (please James, write a comment about what yhis method is doing]
//   returns (b : Object, m : Klon)
//   decreases (m0.oHeap - m0.m.Keys), a.AMFO, (a.fields.Keys), 15 //Clone_Inside_Heap
//
//   //this case
//   requires a !in m0.m.Keys
//   requires inside(a,m0.o)
//
//   //extraOK  requires a.extra == {} //extra not yet clone
//
//
//   //all Clone_
//   requires m0.calid()
//   requires a in m0.oHeap
//   requires COK(a, m0.oHeap)
//
//   //from clone extra owners
//   ensures  m.calid() //needed to be able to call some of the below  en
//   //ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...  //kathump
//   ensures  m.from(m0)
//
//   // ensures  a !in m0.m.Keys ==> b !in m0.ns
//   // ensures  b  in m0.ns ==> a  in m0.m.Keys
//
// { //kathump
//
//   m := Clone_All_Owners(a, m0);
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
//   assert  m.from(m0);
//
//
//   //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //  //
//
//   // assert  a !in m0.m.Keys ==> b !in m0.ns;
//   // assert  b  in m0.ns ==> a  in m0.m.Keys;
// }


//r2

//   //this case
//   requires inside(a,m0.o)
//   requires a.region.World?
//   requires a !in m0.m.Keys

//   //extraOK  requires a.extra == {} //extra not yet cloned

//   //all Clone_
//   requires m0.calid()
//   requires a in m0.oHeap
//   requires COK(a, m0.oHeap)


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
//   ensures  mapLEQ(m0.m,m.m)
//   ensures  m.m.Keys >= m0.m.Keys + {a}
//   ensures  m.m.Values >= m0.m.Values + {b}
//   ensures  m.o == m0.o
//   ensures  m.oHeap == m0.oHeap
//   ensures  m.ns >= m0.ns
//   //  ensures  if (inside(a, m0.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//   ensures m.from(m0)

//   ensures b.fieldModes == a.fieldModes
//   //   ensures b.fields.Keys == a.fields.Keys
//   // ensures  a !in m0.m.Keys ==> b !in m0.ns  //KJX sure about this?
//   modifies {}
// {
//   m := m0;

//   //  assert  m.m.Keys >= m0.m.Keys + {a};
//   //  assert  m.m.Values >= m0.m.Values + {b};

//   print "VARIANT CIW ", |(m0.oHeap - m0.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

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

//   assert  mx.m.Keys >= m0.m.Keys + {a};
//   assert  mx.m.Values >= m0.m.Values + {b};

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

//   assert  m.m.Keys >= m0.m.Keys + {a};
//   assert  m.m.Values >= m0.m.Values + {b};

// }






















// method Clone_Field_Map(a : Object, n : string, b : Object, m0 : Klon)
//   returns (m : Klon)
//   //clone field a.n into b.n
//   //a should be preexisting (in m0.oHeapl); b should be "new" (in m0.ns)
//
//   decreases (m0.oHeap - m0.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5 //Clone_Field_Map
//
//   requires MPRIME: m0.calid()
//   requires COK(a, m0.oHeap)
//   requires COK(b, m0.oHeap+m0.ns)
//   requires COKbm0: COK(b, m0.oHeap+m0.ns)
//
//   requires n  in a.fields.Keys
//   requires n !in b.fields.Keys
//
//   requires n  in a.fieldModes
//   requires n  in b.fieldModes
//   requires a.fieldModes == b.fieldModes
//   requires FLDMODZ: a.fieldModes == b.fieldModes
//
//
//   requires a in m0.oHeap
//   requires a in m0.m.Keys
//   requires a.AMFO <= m0.m.Keys //KJX should be part of some invariant
//
//   requires b in m0.ns
//   requires b in m0.m.Values
// //  requires b.AMFO <= m0.m.Values //KJX should be part of some invariant - also
//   requires b.AMFO <= m0.oHeap+m0.ns
//
//   requires (a in m0.m.Keys) && m0.m[a] == b
//   requires m0.o    in m0.oHeap
//   requires m0.m.Keys   <= m0.oHeap
//
//
//     //not sure why I'd need this..
//   requires forall n <- b.fields :: (n in b.fieldModes) &&
//                                    AssignmentCompatible(b, b.fieldModes[n], b.fields[n])
//
//   //consequently
//   requires refOK(a, a.fields[n])
//
//
//
//   ensures  b.fields.Keys == old(b.fields.Keys) + {n}
//   ensures  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys)
//   ensures  m.calid()
//   ensures  old(m0.calid())
//
//
//   ensures  a in m.m.Keys
//   ensures  (a in m.m.Keys) && m.m[a] == b
//
//   ensures  n in b.fields
//   ensures  (a.fields[n] in m.m.Keys) && m.m[a.fields[n]] == b.fields[n]
//
//   ensures  b in m.m.Values
//
//   ensures  mapLEQ(m0.m,m.m)
//
//   ensures  CallOK(m.oHeap)
//   ensures  COK(a, m.oHeap)
//   ensures  COK(b, m.oHeap+m.ns)
//   ensures  CallOK(m.m.Values, m.oHeap+m.ns)
//   ensures  CallOK(m.ns, m.oHeap+m.ns)
//
//   ensures  m.o     == m0.o
//   ensures  m.oHeap == m0.oHeap
//   ensures  m.ns    >= m0.ns
//   ensures  m.m.Keys    >= m0.m.Keys
//   ensures  m.m.Values    >= m0.m.Values
//   ensures  m.m.Keys    <= m.oHeap
//
//
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys // shoulnd't that be requires
//
//   ensures old(m0.calid())
//   ensures m.from(m0)
//
//   ensures a.fieldModes == b.fieldModes
//
//   ensures  unchanged(a)
//   ensures  unchanged(m0.oHeap)
//   ensures  unchanged(m0.m.Values - {b})
//   ensures  unchanged(m0.m.Keys)
//
//   //ensures  a !in m0.m.Keys ==> b !in m0.ns  //KJX sure about this?
//   //  in this case, a should be in kis, b in b',ns
//
//   ensures  unchanged(m0.ns - {b})  //will this work?
//
//   //  ensures unchanged(m.m.Values - {b}) //duesb;t veruft....
//
//   //  modifies (set o : Object | o !in m0.oHeap)`fields
//   // modifies (set o : Object | o !in ((m0.oHeap+m0.ns) - {b}))`fields
//   //or can this  be modifies m0.ns?
//   modifies b`fields
// {
//   assert m0.calid() by { reveal MPRIME; }
//   assert unchanged(m0.ns);
//
//   assert klonOwnersAreCompatible(a, b, m0) by {
//       reveal m0.calid(), m0.calidObjects(), m0.calidOK(), m0.calidMap(), m0.calidSheep();
//       assert m0.calidObjects() && m0.calidOK() && m0.calidMap() && m0.calidSheep() && m0.calid();
//       assert klonOwnersAreCompatible(a, b, m0);
//     }
//
//   m := m0;
//
// assert m.from(m0);
// //SPLURGE
// assert (m.calid()) by
// {
//   reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
//   assert m.calidObjects() && m.calidOK() && m.calidMap() && m.calidSheep() && m.calid();
// }
// assert klonOwnersAreCompatible(a, b, m);
// //END SPLURGE
//
//
//
//   var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Clone_Field_Map *variant for decreases clause*
//
// print "CALL Clone_Field_Map ", fmtobj(a), " «", n, "»\n";
//
//   print "VARIANT CFM ", |(m0.oHeap - m0.m.Keys)+{a}|, " ", |a.AMFO|, " ", |(a.fields.Keys - b.fields.Keys - {n})|, " ", 10, "\n";
//
//   var onb := m.ns - {b};
//   var ctx := (m.oHeap+m.ns);
//
//   assert CallOK(onb, ctx) by
//   {
//     assert m.calid(); reveal m.calid(); reveal m.calidOK();
//     assert CallOK(m.ns, m.oHeap+m.ns);
//     CallOKNarrowFocus(onb, m.ns, m.oHeap+m.ns);
//     assert CallOK(onb, m.oHeap+m.ns);
//   }
//
//   assert CallOK(m.oHeap) by {
//     assert m.calid(); reveal m.calid();
//     assert m.calidOK(); reveal m.calidOK();
//     assert CallOK(m.oHeap);
//   }
//
//   assert m.calid();
//   assert old(m0.calid());
//   assert unchanged(m0.ns);
//
//   OutgoingReferencesWithinKlonHeapFromCalid(m);
//   assert forall x <- m.oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m.oHeap);
//
//   assert a in m.oHeap;
//   assert a.Ready();
//   assert a.AllOutgoingReferencesWithinThisHeap(m.oHeap);
//
//   var ofv := COKat(a,n,m.oHeap);
//
//   label B3:
//   assert m0.calid() by { reveal MPRIME; }
//
//
//
//   // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//   var rfv, rm := Clone_Via_Map(ofv, m);
//   // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//
//   label B3X:
//   assert rm.calid();
//   assert rm.from(m);
//   assert klonVMapOK(rm.m);
//   assert rm.m[ofv] == rfv;
//
//   assert RFVCOK: COK(rfv, rm.oHeap+rm.ns) by {
//     assert rfv in rm.m.Values;
//     rm.calidOKFromCalid();
//     assert CallOK(rm.m.Values, rm.oHeap+rm.ns);
//     COKfromCallOK(rfv, rm.m.Values, rm.oHeap+rm.ns);
//   }
//
//   m := rm;
//
//   //SPLURGE
//   assert (m.calid()) by
//   {
//     reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
//     assert m.calidObjects() && m.calidOK() && m.calidMap() && m.calidSheep() && m.calid();
//   }
//   //END SPLURGE
//
//   assert unchanged(m0.ns);
//
// //   assert m0.calid() by { reveal MPRIME; }
// //
// //   assert unchanged@B3(m0.oHeap);
//
//
//   assert rfv in  m.m.Values;
//   // assert rfv in  m.oHeap+m.ns;   //let's see if we need these bits.
//   // assert COK(rfv,m.oHeap+m.ns);
//
// //////ensure cloned field is refOK ////////////
//
//   assert m.calid();
//   assert {a,ofv} <= m.m.Keys;
//   assert b == m.m[a];
//   assert rfv == m.m[ofv];
//
//   assert a in m.m.Keys;
//   assert b == m.m[a];
//
//   klonOwnersAreCompatibleWider(a,b,m0,m);
//   assert klonOwnersAreCompatible(a, b, m);
//   assert klonOwnersAreCompatible(ofv, rfv, m);
//   assert refOK(a,ofv);
//
//   // assert m.boundsNestingOK(a, m.oHeap);
//   // assert m.boundsNestingOK(b, m.oHeap+m.ns);
//   // assert (b.AMFO >= b.AMFB >= a.AMFB);
//   //
// klonFieldsAreCompatible(a,ofv,b,rfv,m);
// //
// //   assert refOK(a, ofv);
// //
// // if (outside(ofv,m.o)) {
// // //
// // //
// //
// //           assert
// //             (&& klonOwnersAreCompatible(a, b, m)
// //              && klonOwnersAreCompatible(ofv, rfv, m))
// //           by {
// //
// //
// //               assert klonAllOwnersAreCompatible(m);
// //               assert b == m.m[a];
// //               assert klonOwnersAreCompatible(a, b, m);
// //               assert rfv == m.m[ofv];
// //               assert klonOwnersAreCompatible(ofv, rfv, m);
// //           }
// //
// //
// //   assert (b.AMFO >= b.AMFB >= a.AMFB);
// //   assert (rfv.AMFO >= rfv.AMFB >= ofv.AMFB);
// //
// //   assert refOK(a, ofv);
// //   assert boundInsideOwner(a,ofv) || directlyInside(ofv,a);
// //
// //   if (boundInsideOwner(a,ofv)) {
// //       assert a.AMFB >= (ofv.AMFO - {ofv});
// //
// //       assert b.AMFB >= (rfv.AMFO - {rfv});
// //       assert boundInsideOwner(b,rfv);
// //   } else {
// //       assert directlyInside(ofv,a);
// //       assert a.AMFO == (ofv.AMFO - {ofv});
// //
// //
// //       assert b.AMFO == (rfv.AMFO - {rfv});
// //       assert directlyInside(rfv,b);
// //   }
// //
// //   assert boundInsideOwner(b,rfv) || directlyInside(rfv,b);
// //   assert refOK(b, rfv);
// //
// // }//end outside case
// //
// //
// //
// //   assert boundInsideOwner(a, ofv) || directlyInside(ofv,a);
// //   // mapThruKlonPreservesBoundInsideOwner(a, ofv, b, rfv, m);  //KJXFRIDAY13THK
// // //  assert klonRefOK(a, ofv, b, rfv, m);
// //
// //   assert boundInsideOwner(b, rfv) || directlyInside(rfv, b);
//
//   assert refOK(b, rfv);
//
// //////END ensure cloned field is refOK ////////////
//
//
//
// print "ASSUMING ASSIGNMENT COMPATIBLE\n";
//         assuage AssignmentCompatible(b, b.fieldModes[n], rfv);
// print "ASSUMING ASSIGNMENT COMPATIBLE\n";
//
//
// //   assert AssignmentCompatible(b, b.fieldModes[n], rfv)
// //   by {
// //     // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
// //
// //     assert b.fieldModes[n] == a.fieldModes[n];
// //
// //     assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]) by
// //     {
// //       reveal COK();
// //       assert COK(a, m.oHeap);
// //       assert a.Valid();
// //       assert a.AllFieldsContentsConsistentWithTheirDeclaration();
// //       assert forall n <- a.fields.Keys :: AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
// //       assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
// //     }
// //
// //
// //
// //     match (b.fieldModes[n]) {
// //       case Evil =>
// //         assert b.fieldModes[n] == Evil;
// //         EVILisCompatibleWithAnything(b,rfv);
// //         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
// //
// //       case Rep | Owned(_) | Loaned(_) =>
// //         assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
// //         assert ofv == a.fields[n];
// //      //   assert ofv.owner == a; //KJX what should this be>?
// //         assert b == m.m[a];
// //         assert rfv == m.m[ofv];
// //      //   assert b == rfv.owner;
// //         // assert b == m.m[a.fields[n].owner];
// //         // assert b == rfv.owner;
// //         // mapThruKlonPreservesInside(ofv,a, rfv, b, m);   //KJXFRIDAY13TH
// //         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
// //
// //       case Peer =>
// //         assert AssignmentCompatible(a, a.fieldModes[n], ofv);
// //         assert a.owner == ofv.owner;
// //
// //
// //           assert COK(a, m.oHeap);
// //           RVfromCOK(a, m.oHeap);
// //           assert a.OwnersValid();
// //           assert a.owner <= a.AMFO <= m.m.Keys;
// //
// //           assert klonVMapOK(m.m);
// //           assert m.m[a] == b;
// //           // assert (mapThruKlon(a.owner, m) == b.owner);  //KJXOWNERS mapthru KLon.
// //           // assert m.m[ofv] == rfv;
// //           // assert mapThruKlon(ofv.owner, m) == rfv.owner;  //KJXOWNERS
// //
// //           assert b.owner == rfv.owner; //WORK THE FOKKA?
// //
// //           //assuage b.owner == rfv.owner;   //KJXOWNERS
// //
// //         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
// //
// //       case Borrow(pp,bb,nn,ff) =>
// //         assert refOK(a,a.fields[n]);
// //         assert refOK(b,rfv);
// //         assert AssignmentCompatible(b, b.fieldModes[n], rfv);
// //     }
//
//
//
//     // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//     // }
//
//
//
//
//   assert m.calid();
//
//   assert b in m.ns;
//
// assert (b !in m.oHeap) by {
//
//   reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();
//   assert m.calidObjects() && m.calidOK() && m.calidMap() && m.calidSheep() && m.calid();
//
//     bNotInoHeap(b,m);
//     }
//
//   label B4:
//
//   assert m.calidOK() by { reveal m.calid(); }
//   assert m0.calid() by { reveal MPRIME; }
//   assert m.calid() by {  reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep(); }
//
//
//   assert COK(b, rm.oHeap+rm.ns) by
//   {
//     assert b in m0.ns;
//     assert b in m.ns;
//     assert COK(b, m0.oHeap+m0.ns);
//     assert m0.ns <= m.ns;
//     COKWiderContext2(b,m0.oHeap+m0.ns,m.oHeap+m.ns);
//     assert COK(b, m.oHeap+m.ns);
//   }
//
// assert COKB4: COK(b, rm.oHeap+rm.ns);
//
//   assert
//     && CallOK(m.m.Values, m.oHeap+m.ns)
//     && CallOK(m.ns, m.oHeap+m.ns)
//     && ( m.m.Keys    <= m.oHeap )
//   by { reveal m.calid(); reveal m.calidOK(); }
//
//   CallOKNarrowFocus(m.m.Values-{b}, m.m.Values, m.oHeap+m.ns);
//   CallOKNarrowFocus(m.ns-{b}, m.ns, m.oHeap+m.ns);
//
//   assert CallOK(m.m.Values-{b}, m.oHeap+m.ns);
//   assert CallOK(m.ns-{b}, m.oHeap+m.ns);
//
//   assert b in m.ns;
//
//   label JUSTBEFORE:
//
//
//
//   // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//
// //  b.fields := b.fields[n := rfv];
//
//
//   assert COK(rfv, m.oHeap+m.ns) by { reveal RFVCOK; }
//   m.COKput(b, m.oHeap+m.ns, n, rfv);
//   assert b.fields == old(b.fields)[n := rfv];
//   assert COK(b, m.oHeap+m.ns);
//
//   // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//
//
//   assert unchanged(m0.ns - {b});
//
//   assert CallOK(m.m.Values-{b}, m.oHeap+m.ns);
//   assert CallOK(m.ns-{b}, m.oHeap+m.ns);
//   assert Call_NOB: CallOK(m.ns-{b}, m.oHeap+m.ns);
//
//
//   assert m.m[ofv] == rfv;
//   assert rfv in m.m.Values;
//   assert rfv in m.oHeap+m.ns;
//
//
//   if (b != rfv) {
//
//     assert rfv in (m.oHeap+m.ns);
//     if (rfv in m.oHeap)
//        {
//         assert unchanged(m.oHeap);
//         assert unchanged(rfv);
//        } else {
//         assert rfv !in m.oHeap;
//         assert rfv in m.ns;
//         assert unchanged(m0.ns - {b});
//         assert rfv != b;
//         assert unchanged@B3X(rfv);
//        }
//     assert unchanged@B3X(rfv);
//     assert COK(rfv, rm.oHeap+rm.ns) by { reveal RFVCOK; }
//
// //    assert rm == m;
// //    assert rm.from(m);  //HOW ODD
//
//     // m0.calidOKFromCalid();
//     // COKfromCallOK(rfv,m.m.Values, m.oHeap+m.ns);
//     // assert COK(rfv,m.oHeap+m.ns);
//
//     assert COK(b,  m.oHeap+m.ns) by {
//       reveal COK();
//       assert refOK(b, rfv);
//       assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//
//       assert COK(b,  m.oHeap+m.ns);
//     }
//
//   } else {
//     assert b == rfv;// gulp!
//
//     assert COK(b,  m.oHeap+m.ns) by {
//       reveal COK();
//       assert refOK(b, rfv);
//       assert AssignmentCompatible(b, b.fieldModes[n], rfv);
//       assert COK(b,  m.oHeap+m.ns);
//     }
//     assert COK(rfv,m.oHeap+m.ns);
//   }
//
//   assert unchanged(m0.ns - {b});
//
//   assert m0.calid2();
//   assert old(m0.calid());
//
//   assert COK(b, m.oHeap+m.ns) &&  COK(rfv,m.oHeap+m.ns);
//
//
//   //
//   assert   (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys) by {
//     assert a.fields.Keys == old(a.fields.Keys);
//     assert b.fields.Keys == old(b.fields.Keys)+{n};
//   }
//
//
//   assert
//     && CallOK(m.m.Values, m.oHeap+m.ns)
//     && CallOK(m.ns, m.oHeap+m.ns)
//   by {
//     assert CallOK(m.m.Values-{b}, m.oHeap+m.ns); //OK
//     assert CallOK(m.ns-{b}, m.oHeap+m.ns);
//
//     assert COK(b, m.oHeap+m.ns);
//     assert b in  m.oHeap+m.ns by { reveal COK(); }
//     CallOKfromCOK(b, m.oHeap+m.ns);
//     CallOKWiderFocus(m.ns-{b}, {b}, m.oHeap+m.ns);
//   //  assert ((m.ns-{b}) + {b}) == m.ns;   what the FUCK is this doing anyway?
//
//     assert b in m0.m.Values;
//     assert b in  m.m.Values;
//
//     assert m.m.Values <= m.oHeap+m.ns by { reveal m.calid(); reveal m.calidOK(); }
//
//     assert COK(b, m.oHeap+m.ns);
//     assert b in  m.oHeap+m.ns by { reveal COK(); }
//     CallOKfromCOK(b, m.oHeap+m.ns);
//     assert CallOK({b}, m.oHeap+m.ns);
//     assert CallOK(m.ns-{b}, m.oHeap+m.ns);
//
//     if (b in m.ns) {
//       assert b in m.ns;
//       assert COK(b, m.oHeap+m.ns);
//
// //      CallOKWiderFocus(m.ns-{b}, {b}, m.oHeap+m.ns);
//
//       reveal COK(), CallOK();
//       assert forall o <- (m.ns-{b}) :: COK(o, m.oHeap+m.ns);
//       assert forall o <- ({b}) ::  COK(o, m.oHeap+m.ns);
//       assert forall o <- ((m.ns-{b})+{b}) :: COK(o, m.oHeap+m.ns);
//       assert forall o <- (m.ns) :: COK(o, m.oHeap+m.ns);
//       assert CallOK(m.ns, m.oHeap+m.ns);
//     } else {
//       assert b !in m.ns;
//       assert CallOK(m.ns-{b}, m.oHeap+m.ns) by { reveal Call_NOB; }
//       assert (m.ns-{b}) == m.ns;
//       assert CallOK(m.ns, m.oHeap+m.ns);
//     }
//
//
//     CallOKWiderFocus(m.m.Values-{b}, {b}, m.oHeap+m.ns);
//     assert (m.m.Values-{b} + {b}) == m.m.Values;
//
//
//     assert CallOK(m.m.Values, m.oHeap+m.ns);
//     assert CallOK(m.ns, m.oHeap+m.ns);
//   }
//
//   //OLDCALID assert m0.calid()g{ reveal MPRIME; }
//
//   assert  m.calidOK()
//   by {
//     assert old@B4(rm.calidOK());
//     reveal m.calidOK();
//
//     assert old@B4(CallOK(m.m.Values, m.oHeap+m.ns));
//     assert old@B4(CallOK(m.ns, m.oHeap+m.ns));
//
//
//     assert rfv in rm.m.Values;
//     assert rfv in rm.oHeap+rm.ns;
//     assert COK(rfv,m.oHeap+m.ns);
//
//     assert (m.o in  m.oHeap);
//     assert (m.m.Keys <= m.oHeap);
//     assert (m.m.Values <= m.oHeap+m.ns);
//     assert COK(m.o, m.oHeap);
//     assert CallOK(m.oHeap);
//     assert CallOK(m.m.Keys, m.oHeap);
//
//     assert COK(b,m.oHeap+m.ns);
//
//     // assert CallOK(m.m.Values, m.oHeap+m.ns);
//     // assert CallOK(m.ns, m.oHeap+m.ns);
//     assert m.calidOK();
//   }
//
//
//
//
//   assert unchanged(m0.ns - {b});
//
// // IHasCalidObjects(m);
// //
// // assert klonVMapOK(m.m);
// //
// // IHasCalidMap(m);
//
//
//   // requires AllMapEntriesAreUnique(r.m)
//   // requires klonVMapOK(r.m)
//   // requires (forall x <- r.m.Keys :: (not(inside(x,r.o)) ==> (r.m[x] == x)))
//   // requires (forall x <- r.m.Keys, oo <- x.AMFO :: r.m[oo] in r.m[x].AMFO)
//
//   assert m.calid() by
//   {
//     reveal m.calid();
//     reveal m.calidObjects();
//     reveal m.calidOK();
//     reveal m.calidMap();
//     reveal m.calidSheep();
//
//     assert m.calidObjects();
//     assert m.calidOK();
//
//
//     assert AllMapEntriesAreUnique(m.m);
//     assert klonVMapOK(m.m);
//     assert (forall x <- m.m.Keys :: (not(inside(x,m.o)) ==> (m.m[x] == x)));
//   ///  assert (forall x <- m.m.Keys, oo <- x.AMFO :: m.m[oo] in m.m[x].AMFO); ///KJXFRIDAY13TH
//
//
//     assert klonAllOwnersAreCompatible(m);
//     assert m.readyAll();
//     assert allMapOwnersThruKlownOK(m);
//
//     assert m.calidMap();/////////////////////////
//
//     assert m.m.Keys == m.m.Keys;
//     reveal m.AreWeNotMen();
//     assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);
//
//     assert (forall x <- m.m.Keys :: m.AreWeNotMen(x, m));
//     assert (forall x <- m.m.Keys :: x.fieldModes == m.m[x].fieldModes);
//     assert AllMapEntriesAreUnique(m.m);
//
// IHasCalidSheep(m);
//
//     assert m.calidSheep();/////////////////////////
//
//     assert m.calid();
//
//   }
//   //
//   //   assert m0.calid() by {
//   //
//   //      reveal MPRIME; reveal m0.calid();
//   //
//   //      assert old@JUSTBEFORE(m0.calid());
//   //      assert m.calid();
//   //
//   //      assert n !in  old@JUSTBEFORE(b.fields.Keys);
//   //
//   //      assert old(m0.calid());
//   //     }
//
//   assert old(m0.calid());
//
//   MapOKFromCalid(m);
//   assert klonVMapOK(m.m);
//
// } //end Clone: /_Field_Map





lemma KlonKVRestoresReadyAll(k : Object, v : Object, m0 : Klon, m1 : Klon)
   requires klonCanKV(m0, k, v)
   requires m1 == klonKV(m0, k, v)
   requires m0.readyAll()
   requires m1.readyOK(k)
   ensures  m1.readyAll()
  {
    assert m1.m.Keys == m0.m.Keys + {k};
    assert m1.from(m0);

    forall x <- m1.m.Keys
      ensures (m1.readyOK(x)) //by
      {
        if (x in m0.m.Keys) {
          assert x in m0.m.Keys;
          assert m0.readyOK(x);
          assert m1.m[x] == m0.m[x];
          assert m1.readyOK(x) == m0.readyOK(x);
          assert m1.readyOK(x);
        } else {
          assert x !in m0.m.Keys;
          assert x == k;
          assert m1.readyOK(k);
          assert m1.readyOK(x);
        }
      }

    // if you write it this way it doesn't work
    //     if (x == k) {
    //       assert x !in m0.m.Keys;
    //       assert m1.readyOK(k);
    //       assert m1.readyOK(x);
    //     } else {
    //       assert x in m0.m.Keys;
    //       assert m0.readyOK(x);
    //       assert m1.m[x] == m0.m[x];
    //       assert m1.readyOK(x);
    //     }

      assert m1.readyAll();
   }









function fmtklon(m : Klon) : string
 reads m.m.Keys
 {
   "K:" + natToString(|m.m.Keys|) +
     " oH:" +  natToString(|m.oHeap|) +
     " ns:" +  natToString(|m.ns|) +
     " ks=" + fmtnickset( m.m.Keys )
 }