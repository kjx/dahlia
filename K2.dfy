method Klone_Via_Map(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //entry point for Klone - clones a according to map m'
  //call with m' empty
  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 20 //Klone_Via_Map

  requires m'.calid()
  requires a in m'.oHeap  //technically redundant given COKx
  requires COK(a, m'.oHeap)
  requires a !in m'.m.Keys
  requires a !in m'.m.Values

//  //FROMHERE 
//   ensures  m.calid()
// 
//   ensures  a in m.m.Keys
//   ensures  m.m[a] == b
//   ensures  b in m.m.Values
//   ensures  COK(b,m.oHeap+m.ns)
// 
//   //should I package this up - as aw twostate or a onestate?
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.m.Keys >= m'.m.Keys + {a}
//   ensures  m.m.Values >= m'.m.Values + {b}
//   ensures  m.from(m')
// 
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
//   ensures  m.ns >= m'.ns
//   //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures  klonVMapOK(m.m)
//   ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//   // should we say something about b.AMFO?  b.AMFO <= m.m.Values? por again m.hasV(b)?
//   // m.key(a)?  m.val(a)???
//   // should decided whether to do this with AMFOs or owners
//   // and don one one...
//   ensures  m.from(m')
//   ensures b.AMFO == mapThruKlon(a.AMFO, m)
// 
//   // ensures  a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?
//   ensures  unchanged(a)
//   ensures  unchanged(m'.oHeap)
//   ensures  unchanged(m'.ns)
// 
//   ensures b.fieldModes == a.fieldModes
// 
// //TOHERE

  //  ensures  fresh(b)
  //modifies m'[a]
  //  modifies m'.ns`fields //argh. pity so wide
  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  // modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  modifies {} // only modifes objecst allocated after this point?
{
  m := m';
  assert m.m.Keys == m'.m.Keys;

  print "CALL Klone_Via_Map:", fmtobj(a), " pivot:", fmtobj(m.o), "\n";
  print "VARIANT CVM ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 20, "\n";

  assert COKSTART: COK(a, m.oHeap);

  print "Klone_Via_Map started on:", fmtobj(a), "\n";

  //if already in hash table - return it and be done!
  //not sure why this takes sooo long compared to other
  if (a in m.m.Keys) {

            b := m.m[a];   //what no 'putooutside'

            assert m.m.Keys == m'.m.Keys + {a};

            print "RETN Klone_Via_Map: ", fmtobj(a)," already cloned,  returning ",fmtobj(b), "\n";

            return;
  } // a in m.Keys, already cloned

///case analysis...
  if (outside(a,m.o)) {
    print "Klone_Via_Map ", fmtobj(a), " is really outside ", fmtobj(m.o), "so maps to itself (share not clone)\n";

print "gotta setup owners BEFORE callin putin";


      print "Hey Baby let's CLONE Outside\n";

      b := a;

      print "Yay babhy hyou got that done\n";




  print "about to putOutside\n";

  m := m.putout(a);   ///HOPEY?  CHANGEY?

   //m := m.(m:=m.m[a:=b]);

  assert m.m.Keys >= m'.m.Keys + {a};
    print "crashy?  washy?\n";

print "returnin' from the outsidee case\n";

    // assert a !in m'.m.Keys ==> b !in m'.ns;   //KJX sure about this?

    return;  //we may as well just return here.
             //we've done all we need to do.  I think.

  }///END OF THE OUTSIDE CASE
  else
  { //start of the Inside case
print "start of the Inside case\n";
      print "Klone_Via_Map owners:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";

assert ((m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 20
  decreases to
        (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15);

  assert m.m.Keys >= m'.m.Keys;

      b, m := Klone_Klone_Klone(a, m);

  assert m.m.Keys >= m'.m.Keys + {a};

      // assert a !in m'.m.Keys ==> b !in m'.ns;  }  //end of inside case
print "end of the Inside case\n";

  } //end of inside case

  /////////////////////////////////////////////////////////////// 
  //tidying up after the cases..

  //  }
  print "RETN Klone_Via_Map:", fmtobj(a), " pivot:", fmtobj(m.o), "\n";
  assert m.m.Keys >= m'.m.Keys + {a};
}





method Klone_All_Fields(a : Object, b : Object, m' : Klon)
  returns (m : Klon)
  //clone all fields a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns
  decreases (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10 //Klone_All_Fields
// 
//   requires MPRIME: m'.calid()
//   requires COK(a, m'.oHeap)
//   requires COK(b, m'.oHeap+m'.ns)
// 
//   requires b.fields.Keys == {}
// 
//   requires a.fields.Keys <= a.fieldModes.Keys
//   requires a.fieldModes == b.fieldModes
// 
// 
//   requires a in m'.oHeap
//   requires a in m'.m.Keys
// 
//   requires b in m'.m.Values
//   requires b in m'.ns
//   requires (a in m'.m.Keys) && m'.m[a] == b
//   requires m'.o    in m'.oHeap
//   requires m'.m.Keys   <= m'.oHeap
// 
//   requires a.AMFO <= m'.m.Keys  //seems weird but we are populating m, right...
//  
//   
// 
//   ensures  m.calid()
//   ensures  old(m'.calid())
//   ensures  klonVMapOK(m.m)
//   ensures  a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
// 
//   ensures  b.fields.Keys == a.fields.Keys
// 
//   ensures  a in m.m.Keys
//   ensures  (a in m.m.Keys) && m.m[a] == b



//   ensures  b in m.m.Values
// 
//   ensures  mapLEQ(m'.m,m.m)
// 
//   ensures  CallOK(m.oHeap)
//   ensures  COK(a, m.oHeap)
//   ensures  COK(b, m.oHeap+m.ns)
//   ensures  CallOK(m.m.Values, m.oHeap+m.ns)
//   ensures  CallOK(m.ns, m.oHeap+m.ns)
// 
  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap

  ensures  mapLEQ(m'.m,m.m)
  ensures  m.m.Keys >= m'.m.Keys

//   ensures  m.ns    >= m'.ns
//   ensures  m.m.Keys    <= m.oHeap
// 
//   ensures a.fieldModes == b.fieldModes
//   ensures b.fields.Keys == a.fields.Keys
// 
//   ensures  unchanged(a)
//   ensures  unchanged(m'.oHeap)
//   ensures  unchanged(m'.ns - {b})  //will this work?
// 
//   ensures  forall x <- (m.m.Values - {b}) :: old(allocated( x )) ==> unchanged( x ) //duesb;t veruft....

  //  modifies (set o : Object | o !in m'.oHeap)`fields
  // modifies (set o : Object | o !in ((m'.oHeap+m'.ns) - {b}))`fields
  //or can this  be modifies m'.ns?
  modifies b`fields   ///GGRRR
{
  m := m';

  print "CALL Klone_All_Fields: ", fmtobj(a), " pivot:", fmtobj(m.o), "\n";

  print "VARIANT CAF ", |(m'.oHeap - m'.m.Keys +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";
  print "<<<<<<<<<<<\n";
  print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";
  print "<<<<<<<<<<<\n";


  //START OF FIELDS…

  print "<<<<<<<<<<<\n";
  printmapping(m.m);
  print "<<<<<<<<<<<\n";

  var ns : seq<string> := set2seq(a.fields.Keys);

  print "Klone_All_Fields fields:", fmtobj(a), " fields=", fmtseqstr(ns), "\n";




  var rm := m;


  for i := 0 to |ns|

  invariant  m.o     == m'.o
  invariant  m.oHeap == m'.oHeap
  invariant  mapLEQ(m'.m,m.m)
  invariant  m.m.Keys >= m'.m.Keys

  {

    var n : string := ns[i];
    assume n in a.fields;
    var ofv : Object := a.fields[n];

    assert n !in seq2set(ns[..i]);

    print "  TLOOP  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
    print "  TLOOP  (recurse on field ",n,")\n";
    print "  TLOOP m:", |m.oHeap - m.m.Keys|, " m':", |m'.oHeap - m'.m.Keys|, "\n";
    print "  TLOOP b.fieldsKeys==", b.fields.Keys, "\n";
    print "  TINV                ", ns[..i], "\n";
    print "  TLOOPINV            ",seq2set(ns[..i]),"\n";


    print "VARIANT*CAF ", |(m'.oHeap - m'.m.Keys +{a})|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 10, "\n";



    var OLDFLDS := b.fields.Keys;


    var v_caf := ((m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10);
    var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Klone_Field_Map

    print "v_caf ", v_caf, "\n";
    print "v_cfm ", v_cfm, "\n";


    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) >  (m.oHeap - m.m.Keys +{a}), "\n";
    print "okaoka ", (m'.oHeap - m'.m.Keys +{a}) == (m.oHeap - m.m.Keys +{a}), "\n";

assert ((m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10 
  decreases to
        (m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5 );

    rm := Klone_Field_Map(a,n,b,m);

    m := rm;

  } //end of loop

  print "RETN Klone_All_Fields done ", fmtobj(a), "\n";


  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,m.m);
  assert  m.m.Keys >= m'.m.Keys;

  return;
}
//end Klone_All_Fields



  method Klone_Klone_Klone(a : Object, m' : Klon)
  returns (b : Object, m : Klon)
  //actually does the clone....
  // was the old Klone_Inside_Heap
//  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15 
  decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15 


  //this case
  requires inside(a,m'.o)
  requires a !in m'.m.Keys

  //all Klone_
  requires m'.calid()
  requires a in m'.oHeap
  requires COK(a, m'.oHeap)
// 
//   ensures  m.calid()
//   ensures  a in m.m.Keys
//   ensures  b in m.m.Values
//   ensures  a in m.m.Keys && m.at(a) == b
// //  ensures  b in m.ns
// //  ensures  COK(b, m.oHeap+m.ns)
// 
//   //should I package this up - as aw twostate or a onestate?
//   //it;s about clonbamps, so clonmapLEQ or clonmapEXTENDS
  ensures  mapLEQ(m'.m,m.m)
  ensures  m.m.Keys >= m'.m.Keys + {a}
//   ensures  m.m.Values >= m'.m.Values + {b}
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
//   ensures  m.ns >= m'.ns
//   //  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//   //  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys  //seems weird but we are populating m, right...
//   ensures old(m'.calid())
//   ensures m.from(m')
// // 
// //   //ensures b.AMFO == set x <- a.AMFO :: m.m[x]
// // 
//   ensures b.fieldModes == a.fieldModes
//   //   ensures b.fields.Keys == a.fields.Keys

  //modifies (set o : Object | o !in (m'.oHeap+m'.ns))`fields
  //modifies (set o : Object)`fields
  // ensures a !in m'.m.Keys ==> b !in m'.ns  //KJX sure about this?   //Cline INsinside heap
  // ensures b in m'.ns ==> a in m'.m.Keys
  modifies {}
{ //clone inside heap
  m := m';

  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,m.m);
  assert  m.m.Keys >= m'.m.Keys;

  print "Klone_Klone_CLone of:", fmtobj(a), " owned by ", fmtown(a.owner) ,"\n";
  print "VARIANT CIH ", |(m'.oHeap - m'.m.Keys)|, " ", |a.AMFO|, " ", |(a.fields.Keys)|, " ", 15, "\n";

  
  print "Klone_Klone_CLone ", fmtobj(a), " calling Klone_All_Owners", fmtown(a.owner) ,"\n";

assume m'.oHeap == m.oHeap; 
assume m'.m.Keys <= m.m.Keys;
assert (m'.oHeap - m'.m.Keys) >= (m.oHeap - m.m.Keys);
var    ohprime := (m'.oHeap - m'.m.Keys);
var    noprime := (m.oHeap  - m.m.Keys);
assert ohprime >= noprime;
assert (ohprime,10 decreases to noprime,5);
assert ((m'.oHeap - m'.m.Keys),10 decreases to (m.oHeap - m.m.Keys),5);

  assert ((m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 15
    decreases to 
      (m.oHeap - m.m.Keys), a.AMFO, (a.fields.Keys), 12);

  var rm := Klone_All_Owners(a, m);

  assert  rm.o     == m'.o;
  assert  rm.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,rm.m);
  assert  rm.m.Keys >= m'.m.Keys;

assume a.owner <= rm.m.Keys;
  var rowner := mapThruKlon(a.owner, rm);

assume a.allExternalOwners() <= rm.m.Keys;
  var rAMXO  := mapThruKlon(a.allExternalOwners(),  rm);

  print "Klone_Klone_CLone ", fmtobj(a), " Klone_All_Owners RETURNS ", fmtown(rowner) ,"\n";

  if (a in rm.m.Keys) {

    print "Klone_Klone_CLone ", fmtobj(a), " already cloned: abandoning ship!!\n";



    assume rm.calid();
    assume a in rm.m.Keys;
    b := rm.at(a);


  assert  rm.o     == m'.o;
  assert  rm.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,rm.m);
  assert  rm.m.Keys >= m'.m.Keys;

      m := rm;

    return;
  } // a in rm.m.Keys - i.e. randomly done while cloning owners

  print "Klone_Klone_CLone ", fmtobj(a), " have rowner ", fmtown(rowner) ," self not yet cloned\n";

var rrm := rm; //KJX THIS IS EVIL, should clean up and get rid of rrm completel6.

print "Klone_Klone_Klone ", fmtobj(a), " boodle boodle boodle\n";

  var context := rrm.oHeap+rrm.ns;    ///why haul ns in here??? --- cos this the owners for the clone!  - the clowners!


print "CALLING FAKE...";
  b := new Object.fake(a.fieldModes, rowner, rrm.oHeap+rrm.ns, "clone of " + a.nick);
print "BACK FROM FAKE with ",fmtobj(b),"\n";


  assert  rrm.o     == m'.o;
  assert  rrm.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,rrm.m);
  assert  rrm.m.Keys >= m'.m.Keys;

assume klonCanKV(rrm, a, b);
  var xm := rrm.putin(a,b);

  print "Klone_CLone_Klone map updated ", fmtobj(a), ":=", fmtobj(b) ,"\n";


print "FUCKFUCKFUCK  Klone_All_Fields commented out\n";


assert (
    (m'.oHeap - m'.m.Keys),      a.AMFO, (a.fields.Keys), 15 
  decreases to 
    (xm.oHeap - xm.m.Keys +{a}), a.AMFO, (a.fields.Keys), 10);

  assert  xm.o     == m'.o;
  assert  xm.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,xm.m);
  assert  xm.m.Keys >= m'.m.Keys + {a};


   m := Klone_All_Fields(a,b, xm);

  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,m.m);
  assert  m.m.Keys >= m'.m.Keys;


  print "Klone_Klone_CLone of ", fmtobj(a), " retuning ", fmtobj(b) ,"\n";
}













method Klone_Field_Map(a : Object, n : string, b : Object, m' : Klon)
  returns (m : Klon)
  //clone field a.n into b.n
  //a should be preexisting (in m'.oHeapl); b should be "new"  in m'.ns

  decreases (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5 //Klone_Field_Map
// 
//   requires MPRIME: m'.calid()
//   requires COK(a, m'.oHeap)
//   requires COK(b, m'.oHeap+m'.ns)
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
//   requires a in m'.oHeap
//   requires a in m'.m.Keys
//   requires a.AMFO <= m'.m.Keys //KJX should be part of some invariant
// 
//   requires b in m'.ns
//   requires b in m'.m.Values
//   requires b.AMFO <= m'.m.Keys //KJX should be part of some invariant - also 
//   
// 
//   requires (a in m'.m.Keys) && m'.m[a] == b
//   requires m'.o    in m'.oHeap
//   requires m'.m.Keys   <= m'.oHeap
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
//   ensures  old(m'.calid())
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
  ensures  mapLEQ(m'.m,m.m)
// 
//   ensures  CallOK(m.oHeap)
//   ensures  COK(a, m.oHeap)
//   ensures  COK(b, m.oHeap+m.ns)
//   ensures  CallOK(m.m.Values, m.oHeap+m.ns)
//   ensures  CallOK(m.ns, m.oHeap+m.ns)
// 
  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap
//   ensures  m.ns    >= m'.ns
  ensures  m.m.Keys    >= m'.m.Keys
//   ensures  m.m.Values    >= m'.m.Values
//   ensures  m.m.Keys    <= m.oHeap
// 
// 
//   ensures klonVMapOK(m.m)
//   ensures a.AMFO <= m.m.Keys // shoulnd't that be requires
// 
//   ensures old(m'.calid())
//   ensures m.from(m')
// 
//   ensures a.fieldModes == b.fieldModes
// 
//   ensures  unchanged(a)
//   ensures  unchanged(m'.oHeap)
//   ensures  unchanged(m'.m.Values - {b})
//   ensures  unchanged(m'.m.Keys)

  // ensures  unchanged(m'.ns - {b})  //will this work?

  modifies b`fields
{
  m := m';


  var v_cfm := ((m.oHeap - m.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5);//Klone_Field_Map

print "CALL Klone_Field_Map ", fmtobj(a), " «", n, "»\n";

  print "VARIANT CFM ", |(m'.oHeap - m'.m.Keys)+{a}|, " ", |a.AMFO|, " ", |(a.fields.Keys - b.fields.Keys - {n})|, " ", 10, "\n";

  var onb := m.ns - {b};
  var ctx := (m.oHeap+m.ns);

assume n in a.fields;
assume COK(a,m.oHeap);
assume CallOK(m.oHeap);

  var ofv := COKat(a,n,m.oHeap);

assume m.calid();


assume a in m'.m.Keys;
assume a in m'.oHeap;

assert (
    (m'.oHeap - m'.m.Keys + {a})
    decreases to
      (m.oHeap - m.m.Keys));

assert (
    (m'.oHeap - m'.m.Keys +{a}), a.AMFO, (a.fields.Keys - b.fields.Keys), 5 
  decreases to
    (m.oHeap - m.m.Keys), ofv.AMFO, (ofv.fields.Keys), 20);


  assert  m.o     == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,m.m);
  assert  m.m.Keys >= m'.m.Keys;

assume ofv !in m.m.Keys;
assume ofv !in m.m.Values;

  var rfv, rm := Klone_Via_Map(ofv, m);

  assert  rm.o     == m'.o;
  assert  rm.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,rm.m);
  assert  rm.m.Keys >= m'.m.Keys;

  m := rm;

  b.fields := b.fields[n := rfv];
  
} //end Klone: /_Field_Map





 method Klone_All_Owners(a : Object,  m' : Klon)  returns (m : Klon)
  //adds all thers owners of a into the map
  //decreases (m'.oHeap - m'.m.Keys), a.AMFO, (a.fields.Keys), 12
  decreases (m'.oHeap - m'.m.Keys + {a}), a.AMFO, (a.fields.Keys), 12

// 
//   requires a !in m'.m.Keys //mustn't have cloned a yet...
//   requires COK(a, m'.oHeap)
//   requires m'.calid()
// 
//   ensures  m.calid()

  ensures  mapLEQ(m'.m,m.m)
  ensures  m.m.Keys >= m'.m.Keys
  ensures  m.o     == m'.o
  ensures  m.oHeap == m'.oHeap

//   //ensures  a !in m.m.Keys //can't ensures this cos an onwer could have a pointer to "a"
// 
//   ensures m.from(m')
//   ensures a.owner <= m.m.Keys
//   ensures a.allExternalOwners() <= m.m.Keys
  modifies {}
{
  m := m';
  var rm := m';
  
  var b : Object;  //do we care..

  var xm := rm; 
  assert  xm.o     == m'.o;
  assert  xm.oHeap == m'.oHeap;
  assert  mapLEQ(m'.m,xm.m);
  assert  xm.m.Keys >= m'.m.Keys;

  assert  xm.m.Keys == m'.m.Keys;

  var xo : Object;
  var rr : Object;
  var oldmks  : set<Object>;  //dont fucking ask
  var oldmok :=  false;
  
  assert m'.oHeap == rm.oHeap == xm.oHeap;
  var MX := a.owner - xm.m.Keys;



  while ((MX != {}) && (a !in xm.m.Keys))
    decreases MX
    invariant  MX == a.owner - xm.m.Keys
    invariant  m.oHeap == m'.oHeap == rm.oHeap == xm.oHeap 
    invariant  m.o == rm.o == xm.o == m'.o
    invariant  mapLEQ(m'.m,m.m)
    invariant  mapLEQ(m'.m,rm.m)
    invariant  mapLEQ(m'.m,xm.m)
    invariant  m.m.Keys >= m'.m.Keys
    invariant  rm.m.Keys >= m'.m.Keys
    invariant  xm.m.Keys >= m'.m.Keys        
    {      
    xo :| xo in MX;

    MX := MX - {xo};

    assume xm.calid();
    assume xo in xm.oHeap; 
    assume COK(xo, xm.oHeap);
    assume a in m'.oHeap;
    assume a in m'.m.Keys;
    assume a in xm.m.Keys;

    assert m'.oHeap == xm.oHeap;

assert (({1,2,3}) decreases to ({1,3}));
    
    assert (xm.m.Keys + {a}) > (m'.m.Keys);


assert ((xm.m.Keys + {a}) decreases to (m'.m.Keys));

assert (m'.oHeap - m'.m.Keys + {a}
  decreases to
    xm.oHeap - xm.m.Keys);


assert (
    (m'.oHeap - m'.m.Keys) + {a}, a.AMFO, (a.fields.Keys), 12
      decreases to
    (xm.oHeap - xm.m.Keys), xo.AMFO, (xo.fields.Keys), 20  
 ) by {
  assert m'.oHeap == xm.oHeap;
  assert m.m.Keys >= m'.m.Keys;
  assert rm.m.Keys >= m'.m.Keys;
  assert xm.m.Keys >= m'.m.Keys ;
}

    assume xo !in xm.m.Keys;
    assume xo !in xm.m.Values;


    rr, rm := Klone_Via_Map(xo, xm);

    assert rm.m.Keys > xm.m.Keys;    
    assert rm.oHeap == xm.oHeap;

    if (a in rm.m.Keys) {
      m := rm;
      b := m.m[a];
    return;
    } // a in rm.m.Keys - i.e. randomly done while cloning owners      

    MX := MX - rm.m.Keys;

    oldmks := xm.m.Keys;
    oldmok := true;
    xm := rm;
  } // end loop MX

 m := xm;
}



lemma AGoodAddress<K,V>(k : K, m : map<K,V>) 
  requires k    in m.Keys
  ensures  m[k] in m.Values
{}  
 

lemma GoodAddresses<K,V>(m : map<K,V>) 
  ensures forall k <- m.Keys :: m[k] in m.Values
{}

lemma CallHerPresident(a : Object, m : Klon)
  requires m.calid()
  requires a in m.m.Keys
//  ensures  m.m[a].owner <= m.m.Values
  {  
    reveal m.calid();
    assert m.calid();
    reveal m.calidMap();
    assert m.calidMap();

    assert klonVMapOK(m.m);

    assert //from klonVMapOK(m)
      && (forall k <- m.m.Keys :: k.AMFO <= m.m.Keys)
      && (forall k <- m.m.Keys :: mapThruVMap(k.AMFO, m.m) == m.m[k].AMFO)
      && (forall k <- m.m.Keys :: k.owner <= k.AMFO)
      && (forall k <- m.m.Keys :: k.owner <= m.m.Keys)
    ;

    assert (forall k <- m.m.Keys :: k.owner <= k.AMFO <= m.m.Keys);

    // forall k : Object | k in m.m[a].owner 
    //   ensures ( k in m.m.Values ) {
    //     assert a in m.m.Keys;
    //     assert k in m.m[a].owner;        
    //     AGoodAddress(a, m.m);
    //     assert m.m[a] in m.m.Values;
    //     assert k in m.m.Values;
    //   }
    
    forall k : Object | k in m.m.Keys
      ensures ( m.m[k] in m.m.Values ) {
        assert k in m.m.Keys;
        AGoodAddress(k, m.m);      
        assert m.m[k] in m.m.Values;
      }
    
    assert a       in m.m.Keys;
    assert a.owner <= m.m.Keys;
    assert forall ao <- a.AMFO :: m.m[ao] in m.m[a].AMFO;
  //  assert mapThruKlon(a.owner, m) == m.m[a].owner; 

    mapThruKlonPreservesSubsets(a.AMFO, m.m.Keys, m);

    assert mapThruKlon(m.m.Keys, m) == m.m.Values;

    mapThruKlonPreservesSubsets(a.owner, a.AMFO, m);
    mapThruKlonPreservesSubsets(a.owner, m.m.Keys, m);

    assert mapThruKlon(a.owner, m) <= m.m.Values;



//    assert m.m[a].owner <= m.m.Values;

    // 
    //   && (forall k <- m.m.Keys :: mapThruVMap(k.owner, m.m) == m.m[k].owner)
    // ;

  }



lemma HeyOwner(a : Object, m : Klon)
  requires m.calid()
  requires a in m.m.Keys
{
  var b := m.m[a];

    reveal m.calid();
    assert m.calid();
    reveal m.calidMap();
    assert m.calidMap();

    assert klonVMapOK(m.m);

    assert //from klonVMapOK(m)
      && (forall k <- m.m.Keys :: k.AMFO <= m.m.Keys)
      && (forall k <- m.m.Keys :: mapThruVMap(k.AMFO, m.m) == m.m[k].AMFO)
      && (forall k <- m.m.Keys :: k.owner <= k.AMFO)
      && (forall k <- m.m.Keys :: k.owner <= m.m.Keys)
    ;

    assert (forall k <- m.m.Keys :: k.owner <= k.AMFO <= m.m.Keys);


// assert a.AMFO == flattenAMFOs(a.owner) + {a};
// assert mapThruKlon({a},m) == {b};

}

lemma MapFlat(os : set<Object>, m : Klon)
  requires os <= m.m.Keys
  requires flattenAMFOs(os) <= m.m.Keys;
{
   var mos  := mapThruKlon(os, m);
   var fmos := flattenAMFOs(mos);

   var fos  := flattenAMFOs(os);
   var mfos := mapThruKlon(fos, m);

//   assert fmos == mfos;

   var xmos := set o <- os :: m.m[o];
   assert xmos == mos;

   var xfos := os + (set o <- os, oo <- o.AMFO :: oo);
   assert xfos == fos;

   var fxmos := flattenAMFOs(xmos);
   assert fxmos == fmos;

   var mxfos := mapThruKlon(xfos, m);
   assert mxfos == mfos;

   var xmxfos :=  set o <- xfos :: m.m[o];
   assert xmxfos == mfos;

   var xfxmos := xmos + (set o <- xmos, oo <- o.AMFO :: oo);
//   assert xfxmos == xmxfos;
   
//assert fxmos == mxfos;

}


lemma vmapOKowners(m : vmap<Object,Object>, ks : set<Object> := m.Keys)
  requires ks <= m.Keys
  requires klonVMapOK(m, ks)
  ensures 
    && (forall k <- ks :: k.owner <= m.Keys)
    && (forall k <- ks :: mapThruVMap(k.owner, m) == m[k].owner)
{
  assume
  && (forall k <- ks :: k.owner <= m.Keys)
  && (forall k <- ks :: mapThruVMap(k.owner, m) == m[k].owner)  
  ;
}
