

method clone(a : Object, context : set<Object>,  into : Owner := a.owner)
    returns (b : Object, subtext : set<Object>)

  requires COK(a, context)
  requires flatten(into) >= a.AMFB
  requires CallOK(context)
  requires forall x <- context :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(context)
{
  var m' : Klon := Klon(map[],    //m clonemap
               a,       // o - object to be cloned / pivot / top object
               a.AMFO,  // o_amfo AMFO of o
               into,    // c_owner - proposewd owner of clone
               flatten(into),   // c_amfx - AMFX of clone
               {},
               {},
               context,      // oHeap
               {}            // ns );
              );

  assert a in context;
  assert m'.m.Keys == {} == m'.m.Values;

  assert m'.calid() by {

    reveal m'.calidObjects(); assert m'.calidObjects();
    reveal m'.calidOK();

    assert (m'.o in m'.oHeap);
    assert (m'.m.Keys <= m'.oHeap);
    assert (m'.m.Values <= m'.oHeap+m'.ns);
    assert COK(m'.o, m'.oHeap);
    assert CallOK(m'.oHeap);

    reveal CallOK();
    assert CallOK(m'.m.Keys, m'.oHeap) by { assert m'.m.Keys == {}; }
    assert CallOK(m'.m.Values, m'.oHeap+m'.ns) by { assert m'.m.Values == {}; }
    assert CallOK(m'.ns, m'.oHeap+m'.ns) by { assert m'.ns == {}; }

    assert forall x <- m'.oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(m'.oHeap);


    assert m'.calidOK();
    reveal m'.calidMap();     assert m'.calidMap();
    reveal m'.calidSheep();   assert m'.calidSheep();

    reveal m'.calid();        assert m'.calid();
  }


//  assert m'.readyAll() by { assert m'.m.Keys == {}; }

  assert allMapOwnersThruKlownOK(m');

  assert klonCanKV(m',a,a);  //hmm, interesting... technically not right but;

  var m0 : Klon := seed(a, into, context);
  var m1 : Klon;

  b, m1 := Xlone_Via_Map(a, m0);

  subtext := m1.ns;
}


function seed(o : Object, clowner : Owner, oHeap : set<Object>) : (m : Klon)
    requires COK(o, oHeap)
    requires CallOK(oHeap)
    requires forall x <- oHeap :: x.Ready() && x.AllOutgoingReferencesWithinThisHeap(oHeap)
    ensures  m.ownersInKlown(o)

    reads oHeap`fields, oHeap`fieldModes
    {

    var mep0 := map x <- o.AMFX :: x;

    var clamfx := flatten(clowner);

    reveal UniqueMapEntry();
    assert forall i <- mep0.Keys :: UniqueMapEntry(mep0, i);
    assert AllMapEntriesAreUnique(mep0);

    var mep : vmap<Object,Object> := mep0;

    assert mep.Keys == mep.Values == o.AMFX <= oHeap by  { reveal COK(); }

    var mTKoA := mapThruVMap(o.AMFX, mep);
    var cxtra := clamfx - mTKoA;
    var oxtra := mTKoA - clamfx;


    var m : Klon := Klon(mep,
        o,
        o.AMFX,
        clowner,
        clamfx,
        oxtra,
        cxtra,
        oHeap,
        {} );

    assert m.ns == {};

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
        assert (forall x <- m.m.Keys ::
                m.BoundsNestingFromCOK(x, m.oHeap);
                && m.boundsNestingOK(x, m.oHeap)
                && m.boundsNestingOK(m.m[x], m.oHeap+m.ns)
                && m.fieldMappingsOK(x, m.m[x], m.m.Keys));

        assert (klonAllOwnersAreCompatible(m)) by {
           forall o <- m.m.Keys ensures klonOwnersAreCompatible(o,m.m[o],m) //by
            {
            assert m.boundsNestingOK(o, m.oHeap);
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

    assert m.calid();

    m
    }
