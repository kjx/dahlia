



method Clone_Via_MIN(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //entry point for Clone - clones a according to map m'
  //call with m' empty
  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 20 //Klone_Via_Map

  requires m'.calid()
  requires m'.readyAll()
  requires klonAllRefsOK(m')
  requires a in m'.oHeap  //technically redundant given COKx
  requires COK(a, m'.oHeap) //ties owners into OHEAP but not KLON MAP






 //FROMHERE
  ensures  m.calid()

  ensures  a in m.m.Keys
  ensures  m.m[a] == b
//  ensures  COK(b,m.oHeap+m.ns) ///shojuld beaable to get this

  //should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
//   ensures  m.m.Keys >= m'.m.Keys + {a}
//   ensures  m.m.Values >= m'.m.Values + {b}
//   ensures  m.from(m')

//   ensures  m.o == m'.o
//   ensures  m.oHeap == m'.oHeap
//   ensures  m.ns >= m'.ns

  //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)

  ensures  klonVMapOK(m.m)
  ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
  // should we say something about b.AMFO?  b.AMFO <= m.m.Values? por again m.hasV(b)?
  // m.key(a)?  m.val(a)???
  // should decided whether to do this with AMFOs or owners
  // and don one one...
  //OK os THIS requires us to make sure all the owners are in (even if outsidef - where does that happen?)
//  ensures  m.from(m')
  //ensures b.AMFO == mapThruKlon(a.AMFO, m) //hmmm - bit it's NOT there

  // ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
  ensures  unchanged(m'.ns)

  ensures klonOwnersAreCompatible(a, b, m)
  ensures m.readyAll()

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

  if (a in m.m.Keys){ //already cloned, return
    b := m.m[a];
    assume klonOwnersAreCompatible(a, b, m);  //FUCK
    assume  klonVMapOK(m.m);                  //FUCK
    return;
  }

  if (outside(a,m.o)) { //outside. so just map to itself
    b := a;
    assert m.readyAll();
    assume klonCanKV(m,a,a);                  //FUCK
    assert klonAllRefsOK(m);
    assume m.AreWeNotMen(a, klonKV(m,a,a));   //FUCK??
    assume m.m.Keys <= m.oHeap;               //FUCL
    assume a.allExternalOwners() <= m.m.Keys; //FUCK
    assume  forall oo <- a.owner :: outside(oo,m.o);
    m := m.putOutside(a);
    klonSameOwnersAreCompatible(a,a,m);
    assert klonOwnersAreCompatible(a, a, m);  //FUCK
    assume m.readyAll();
    return; // end outside case
  }
  else
  { //start of the Inside case
      b, m := Clone_Clone_Clone(a, m);
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

  assume m.readyAll();
  return;
}
