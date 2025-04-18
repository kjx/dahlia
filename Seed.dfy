

method clone(a : Object, context : set<Object>,  into : Owner := a.owner)
    returns (b : Object, subtext : set<Object>)

  requires COK(a, context)
  requires flatten(into) >= a.AMFB
  requires CallOK(context)
  requires forall x <- context :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(context)
{
  var m0 : Klon := seed(a, into, context);
  var m1 : Klon;

  assert m0.readyAll();

  assert m0.calid();
  assert m0.readyAll();
  assert checkClownershipAllObjects(m0);
  assert COK(a, m0.oHeap);
  assert klonCanKV(m0,a,a);

  b, m1 := Xlone_Via_Map(a, m0); //*

  subtext := m1.ns;
}

//   var m' : Klon := Klon(map[],    //m clonemap
//                a,       // o - object to be cloned / pivot / top object
//                a.AMFO,  // o_amfo AMFO of o
//                into,    // c_owner - proposewd owner of clone
//                flatten(into),   // c_amfx - AMFX of clone
//                {},
//                {},
//                context,      // oHeap
//                {}            // ns );
//               );
//
//   assert a in context;
//   assert m'.m.Keys == {} == m'.m.Values;
//
//   assert m'.calid() by {
//
//     reveal m'.calidObjects(); assert m'.calidObjects();
//     reveal m'.calidOK();
//
//     assert (m'.o in m'.oHeap);
//     assert (m'.m.Keys <= m'.oHeap);
//     assert (m'.m.Values <= m'.oHeap+m'.ns);
//     assert COK(m'.o, m'.oHeap);
//     assert CallOK(m'.oHeap);
//
//     reveal CallOK();
//     assert CallOK(m'.m.Keys, m'.oHeap) by { assert m'.m.Keys == {}; }
//     assert CallOK(m'.m.Values, m'.oHeap+m'.ns) by { assert m'.m.Values == {}; }
//     assert CallOK(m'.ns, m'.oHeap+m'.ns) by { assert m'.ns == {}; }
//
//     assert forall x <- m'.oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m'.oHeap);
//
//
//     assert m'.calidOK();
//     reveal m'.calidMap();     assert m'.calidMap();
//     reveal m'.calidSheep();   assert m'.calidSheep();
//
//     reveal m'.calid();        assert m'.calid();
//   }
//
//
//   assert allMapOwnersThruKlownOK(m');
//
//   assert klonCanKV(m',a,a);
//
// //  assert m'.readyAll() by { assert m'.m.Keys == {}; }
//
//   assert forall o <- m'.m.Keys :: mappingOwnersThruKlownOK(o,m');
//
//   assert allMapOwnersThruKlownOK(m');
//
//   assert klonCanKV(m',a,a);  //hmm, interesting... technically not right but;
//         //not, this IS ruight...



function seed(o : Object, clowner : Owner, oHeap : set<Object>) : (m : Klon)
//seed Klon for cloning object o,  owner of clone being clowner, within heap oHeap...
    requires COK(o, oHeap)
    requires CallOK(oHeap)
    requires forall x <- oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(oHeap)

    ensures m.ownersInKlown(o)
    ensures m.calid()
    ensures m.readyAll()
    ensures COK(o, m.oHeap)
    ensures allMapOwnersThruKlownIfInsideOK(m)
//
//     ensures m == Klon( (map x <- o.AMFX :: x),
//         o,
//         o.AMFX,
//         clowner,
//         flatten(clowner),
//         (flatten(clowner) - mapThruKlon(o.AMFX, m)),
//         (mapThruKlon(o.AMFX, m) - flatten(clowner)),
//         oHeap,
//         {} )


    ensures klonCanKV(m,o,o)
    reads oHeap`fields, oHeap`fieldModes
    {

    var mep0 := map x <- o.AMFX :: x;

    var clamfx := flatten(clowner);

    reveal UniqueMapEntry();
    assert forall i <- mep0.Keys :: UniqueMapEntry(mep0, i);
    assert AllMapEntriesAreUnique(mep0);

    var mep : vmap<Object,Object> := mep0;

    assert mep.Keys == mep.Values == o.AMFX <= oHeap by  { reveal COK(); }

    forall o <- mep0.Keys ensures true //by
      {
        assert o.Ready();
        assert o in mep0.Keys;
        //assert mep0.Keys >= o.AMFX >= o.AMFB;
        //assert mep0.Keys >= mep0[o].AMFX >= mep0[o].AMFB;
      }
    var mTKoA := mapThruVMap(o.AMFX, mep);
    var oxtra := mTKoA - clamfx;
    var cxtra := clamfx - mTKoA;

    var m : Klon :=
                       Klon(mep,
                            o,
                            o.AMFX,
                            clowner,
                            clamfx,
                            oxtra,
                            cxtra,
                            oHeap,
                            {} );

    assert m.ns == {};
    assert m.oHeap == oHeap;

    assert o.AMFX == m.o_amfx <= m.m.Keys;

    assert oxtra == m.oxtra == (mapThruKlon(o.AMFX, m) - clamfx);
    assert cxtra == m.cxtra == (clamfx - mapThruKlon(o.AMFX, m));

    assert COK(o, oHeap);
    assert COK(o, m.oHeap);

    reveal m.calid(), m.calidObjects(), m.calidOK(), m.calidMap(), m.calidSheep();

    assert m.calidObjects() by {
        reveal m.calidObjects();

        assert
            && m.o in m.oHeap
            && m.m.Keys <= m.oHeap
            && m.ns !! m.oHeap
            && m.m.Values <= m.ns + m.oHeap
            && m.ns <= m.m.Values
            ;
        }

    assert m.calidOK() by {
        reveal m.calidOK(), m.calidObjects();
        assert m.calidObjects();
        reveal COK(), CallOK();
        assert (m.m.Keys == m.m.Values == o.AMFX <= m.oHeap);


        assert
            && (m.o in m.oHeap)
            && (m.m.Keys <= m.oHeap)
            && (m.m.Values <= m.oHeap+m.ns)
            && COK(m.o, m.oHeap)
            && CallOK(m.oHeap)
            && CallOK(m.m.Keys, m.oHeap)
            && CallOK(m.m.Values, m.oHeap+m.ns)
            && CallOK(m.ns, m.oHeap+m.ns)
            && (forall x <- m.oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m.oHeap))
            ;
        }


    assert m.calidMap() by {
        reveal m.calidObjects(); assert m.calidObjects();
        reveal m.calidOK(); assert m.calidOK();
        reveal CallOK();
        assert AllMapEntriesAreUnique(m.m);
        assert klonVMapOK(m.m);
        forall x <- m.m.Keys ensures (
                && m.boundsNestingOK(x, m.oHeap)
                && m.boundsNestingOK(m.m[x], m.oHeap+m.ns)
                && m.fieldMappingsOK(x, m.m[x], m.m.Keys)
        ) //by
        {
              m.BoundsNestingFromCOK(x, m.oHeap);
        }

    assert (klonAllOwnersAreCompatible(m)) by {
           forall o <- m.m.Keys ensures klonOwnersAreCompatible(o,m.m[o],m) //by
            {
            assert m.boundsNestingOK(m.m[o], m.oHeap+m.ns);

              assert (m.m[o].AMFO >= m.m[o].AMFB >= m.m[o].AMFB);
            }

        }
        assert (forall x <- m.m.Keys :: (not(inside(x,o)) ==> (m.m[x] == x)));
    }



    assert m.calidSheep() by {
        reveal m.calidObjects(); assert m.calidObjects();
        reveal m.calidOK(); assert m.calidOK();

        reveal m.AreWeNotMen();
        assert
            && (forall x <- m.m.Keys :: m.AreWeNotMen(x, m))
            && (forall x <- m.m.Keys :: x.fieldModes == m.m[x].fieldModes)
            && (AllMapEntriesAreUnique(m.m))
            ;
    }

    assert m.oHeap == oHeap;
    assert m.calid();



    assert m.readyAll() by {
      assert o.AMFX == m.o_amfx <= m.m.Keys;

      assert oxtra == m.oxtra == (mapThruKlon(o.AMFX, m) - clamfx);
      assert cxtra == m.cxtra == (clamfx - mapThruKlon(o.AMFX, m));


      forall o <- m.m.Keys ensures m.readyOK(o) //by
        {
          assert o.Ready();
          assert o in m.m.Keys;
          assert m.ownersInKlown(o);
        } //end forall
    } //end assert/by

    assert klonCanKV(m,o,o) by {
      var c' := m;
      var k  := o;
      var v := o;

      var ks := c'.m.Keys+{k};

reveal m.calid(), m.calidMap();
assert m.calid();
assert m.calidMap();

assert

  && klonVMapOK(c'.m) //BOWIE

  && canVMapKV(c'.m, k, v)
  && (k in c'.oHeap)  //KJX do I want this here?
  && (if (v==k) then (v in c'.oHeap) else (v !in c'.oHeap)) //nope - happens after  wards
;

//grrr. should refactor this

  reveal COK(), CallOK();
  assert COK(o, oHeap);
  COKWiderContext2(o, oHeap, c'.oHeap+c'.ns+{o});
  COKNarrowContext(o, c'.m.Keys+{o}, oHeap);

  assert CallOK(oHeap);
  assert forall x <- oHeap :: x.Ready();
  assert forall x <- oHeap :: x.Ready();


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

assert
  && (k.fieldModes == v.fieldModes)

//&& (v.AMFO >= v.AMFB >= k.AMFB)
  && (v.AMFX >= v.AMFB >= k.AMFB)

;

//END DOOUBLE BOWIE


    }

    assert forall o <- m.m.Keys ::  m.m[o] == o;

    assert forall o <- m.m.Keys ::  not(inside(o,m.o));

    assert allMapOwnersThruKlownIfInsideOK(m) by {

      forall o <- m.m.Keys ensures
           mappingOwnersThruKlownIfInsideOK(o,m) // by
       {
        var c := m.m[o];

        assert
            && (c == o)
            && (c.bound == o.bound)
            // && (c.bound == mapThruKlownIfInside(o.bound, m))
            // && (c.AMFB  == mapThruKlownIfInside(o.AMFB,  m))
            // && (c.owner == mapThruKlownIfInside(o.owner, m))
            // && (c.AMFX  == mapThruKlownIfInside(o.AMFX , m))
            // && (c.ntrnl == mapThruKlownIfInside(o.ntrnl, m))
            // && (c.AMFO  == mapThruKlownIfInside(o.AMFO,  m))
        ;
      }
    }

    m

    }
