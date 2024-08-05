





































method  {:verify false } XX_Clone_Field_Map(a : Object, n : string, b : Object, m' : Map) 
   returns (m : Map)
//clone field a.n into b.n
//a should be preexisting (in m'.oHeapl) while≈≈≈≈≈ b should be "new"  in m'.ns


decreases (m'.oHeap - m'.ks + {a}), a.AMFO, (a.fields.Keys - b.fields.Keys - {n}), 10

  requires m'.calid()
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

  requires b.fieldModes[n] == Evil //evilKJX this is actually evil 
                                   //well not *that* evil as I still must satisfy refOK
   
  requires forall n <- b.fields :: (n in b.fieldModes) &&
              AssignmentCompatible(b, b.fieldModes[n], b.fields[n])

  //consequently
  requires refOK(a, a.fields[n])
  requires a.region.Heap? == b.region.Heap?


    
  ensures  b.fields.Keys == old(b.fields.Keys) + {n}
  ensures  (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys)

  ensures  m.calid()

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
  ensures  m.ks    <= m.oHeap 

  ensures a.fieldModes == b.fieldModes

  ensures  unchanged(a)
  ensures  unchanged(m'.oHeap)
//  ensures unchanged(m.vs - {b}) //duesb;t veruft....

  modifies (set o : Object | o !in m'.oHeap)`fields
///  modifies b`fields   ///GGRRR
  {
    assert a.fields.Keys == old(a.fields.Keys);
    assert COK(b, m'.oHeap+ m'.ns);

    m := m';
    
    assert COK(b, m.oHeap+m.ns);
    assert BOK: COK(b, m.oHeap+m.ns);


    print "CFM variant: (",|(m'.oHeap - m'.ks + {a})|,",",|(a.AMFO)|,",10,",|(a.fields.Keys)|,")\n";

 
assert (
 && b !in m.oHeap
) by
{
    reveal m.calid(); assert m.calid();
    reveal m.calidObjects(); assert m.calidObjects();
    reveal m.calidOK(); assert m.calidOK();
  
    reveal m.calidMap(); assert m.calidMap();
    reveal m.calidSheep(); assert m.calidSheep();
    reveal COK(); reveal CallOK();

    assert b in m.ns;
    assert m.ns !! m.oHeap;
    assert b !in m.oHeap;
}

assert (
  && CallOK(m.oHeap)
  && COK(a, m.oHeap)
  && COK(b, m.oHeap + m.ns)
  && CallOK(m.vs, m.oHeap+m.ns)
  && CallOK(m.ns, m.oHeap+m.ns)
) by {
    reveal m.calid(); assert m.calid();
    reveal m.calidObjects(); assert m.calidObjects();
    reveal m.calidOK(); assert m.calidOK();
  
    reveal m.calidMap(); assert m.calidMap();
    reveal m.calidSheep(); assert m.calidSheep();
    reveal COK(); reveal CallOK();
   
    assert a in m.oHeap;
   
    assert unchanged(b);
    assert CallOK(m.oHeap);
    assert COK(a, m.oHeap);
    assert COK(b, m.oHeap + m.ns);
    assert CallOK(m.vs, m.oHeap+m.ns);
    assert CallOK(m.ns, m.oHeap+m.ns);
}  


 assert a.fields.Keys == old(a.fields.Keys);
 
 var onb := m.ns - {b};
 var ctx := (m.oHeap+m.ns);

    assert CallOK(onb, ctx) by
       {
        assert CallOK(m.ns, m.oHeap+m.ns);
        CallOKNarrowFocus(onb, m.ns, m.oHeap+m.ns);
        assert CallOK(onb, m.oHeap+m.ns);
      }


//    var ofv : Object := a.fields[n];

    assert CallOK(m.oHeap) by {
      reveal m.calid(); reveal m.calidOK(); 
      assert m.calid(); assert m.calidOK(); 
      assert CallOK(m.oHeap);
    }



    var ofv := COKat(a,n,m.oHeap);



    print "Clone_Field_Map  a:",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";

// // // // // // // // // // // // // // // // // // // 
    // assert COK(ofv, m.oHeap) by {
    //     reveal m.calid(); reveal m.calidObjects(); reveal m.calidOK(); 
    //     assert m.calid(); assert m.calidObjects(); assert m.calidOK();
    //     reveal CallOK(); reveal COK();
    //     assert   && COK(a, m.oHeap)
    //             && CallOK(m.vs, m.oHeap+m.ns)
    //             && CallOK(m.ns, m.oHeap+m.ns);
    //     assert ofv in m.oHeap;
    //     assert a.Ready();
    //     assert a.AllOutgoingReferencesWithinThisHeap(m.oHeap);
    // }

    assert COK(ofv, m.oHeap);
    assert COK(b, m.oHeap+m.ns);
    assert CallOK(m.oHeap);
    assert CallOK(m.ns, m.oHeap+m.ns);
    assert CallOK(onb, ctx);
    assert CallOK(m.ns-{b},m.oHeap+m.ns);


    assert a.fields.Keys == old(a.fields.Keys);
    

    label B4:
    assert b in m'.ns;
    assert b in m.ns;

    var rfv, rm := Clone_Via_Map(ofv, m);

assert unchanged (m'.oHeap+m'.ns);
// assert forall o <- (rm.oHeap+rm.ns) :: old(allocated(o)) ==> unchanged(o);
    assert unchanged  (set o : Object | o in (m'.oHeap+m'.ns));

    assert b in m'.ns;
    assert unchanged@B4(b);
    assert unchanged(b);
    assert a in m'.oHeap;
    assert unchanged(m'.oHeap);
    assert unchanged(a);
   assert a.fields.Keys == old(a.fields.Keys);


    assert rm.calid();

    assert
      && COK(ofv, m.oHeap)
      && COK(b, m.oHeap+m.ns)
      && CallOK(m.oHeap)
      && CallOK(m.ns, m.oHeap+m.ns)
      && CallOK(onb, ctx)
      && CallOK(m.ns-{b},m.oHeap+m.ns)
    by {
      assert mapLEQ(m.m,rm.m);
      assert m.ks <= rm.ks;
      assert m.vs <= rm.vs;
      assert m.ns <= rm.ns;
      assert onb == m.ns - {b};
      assert ctx == (m.oHeap+m.ns);
      assert CallOK(m.ns-{b},m.oHeap+m.ns);
    }
  

    assert
      && COK(ofv, rm.oHeap)
      && COK(b, rm.oHeap+rm.ns)
      && CallOK(rm.oHeap)
      && CallOK(rm.ns, rm.oHeap+rm.ns)
      && CallOK(onb, ctx)
      && CallOK(rm.ns-{b},rm.oHeap+rm.ns)
    by {
    reveal rm.calid(); assert rm.calid();
    reveal rm.calidObjects(); assert rm.calidObjects();
    reveal rm.calidOK(); assert rm.calidOK();
  
    reveal rm.calidMap(); assert rm.calidMap();
    reveal rm.calidSheep(); assert rm.calidSheep();
    reveal COK(); reveal CallOK();
   
    assert a in rm.oHeap;
  
      assert mapLEQ(rm.m,rm.m);
      assert rm.ks <= rm.ks;
      assert rm.vs <= rm.vs;
      assert rm.ns <= rm.ns;
      // assert onb <= rm.ns - {b};
      // assert ctx <= (rm.oHeap+rm.ns);

        assert CallOK(rm.ns, rm.oHeap+rm.ns);
        CallOKNarrowFocus((rm.ns-{b}), rm.ns, rm.oHeap+rm.ns);
        assert CallOK((rm.ns-{b}), rm.oHeap+rm.ns);

      assert CallOK(rm.ns-{b},rm.oHeap+rm.ns);

    assert unchanged(b);
    assert CallOK(rm.oHeap);
    assert COK(a, rm.oHeap);
    assert COK(b, rm.oHeap + rm.ns);
    assert CallOK(rm.vs, rm.oHeap+rm.ns);
    assert CallOK(rm.ns, rm.oHeap+rm.ns);
}  

     assert a.fields.Keys == old(a.fields.Keys);

  m := rm;

    assert m.calid();

    assert MCALID: m.calid();

    assert CallOK(m.ns, m.oHeap+m.ns);
    assert CallOK(onb, ctx);
    assert CallOK(m.ns-{b},m.oHeap+m.ns);


    assert COK(b, m.oHeap+m.ns);
     
    assert m.calid();


    print "Clone_Field_Map  b",fmtobj(b),".",n," :=", fmtobj(rfv), "\n";

    assert rfv in m.oHeap+m.vs;
    assert COK(rfv,m.oHeap+m.ns);




// 
// assert FallEQ(m.oHeap);
//        
//     reveal m.calid(); assert m.calid();
//     reveal m.calidObjects(); assert m.calidObjects();
//     reveal m.calidOK(); assert m.calidOK();
//     reveal m.calidMap(); assert m.calidMap();
//     reveal m.calidSheep(); assert m.calidSheep();
// 

// 
// 
//     var aa := (m.m.Values - {b});   
//     var context := m.oHeap+m.ns;
// 
//     assert CallOK(m.vs, context);
//     assert m.vs == m.m.Values;
//     assert CallOK(m.m.Values, context);
// 
//     assert CallOK(m.ns, context);
// 
//     assert m.vs <= m.ns + m.oHeap;
//     assert m.m.Values <= m.ns + m.oHeap;
// 
//     assert (CallOK(m.m.Values, context));
// 
//     assert m.oHeap + m.m.Values <= m.oHeap + m.ns;
//     assert aa <= m.m.Values;

 assert a.fields.Keys == old(a.fields.Keys);


    assert COK(b,  m.oHeap+m.ns);
    assert COK(rfv,m.oHeap+m.ns);


    assert CallOK(m.oHeap);
    assert b  in m.ns;
    assert b !in m.oHeap;

    assert CallOK(m.ns, m.oHeap+m.ns);
    CallOKNarrowFocus(m.ns-{b},m.ns,m.oHeap+m.ns); 
    assert CallOK(m.ns-{b}, m.oHeap+m.ns);

var oldFields := b.fields;
assert oldFields == old(b.fields);
assert n !in b.fields;
assert n !in oldFields;

      assert a.fieldModes == old(a.fieldModes);

    assert refOK(b, rfv);
    assert AssignmentCompatible(b, b.fieldModes[n], rfv);


    assert COK(m.o, m.oHeap) by {
      assert m.calid();      
      reveal m.calid();
      reveal m.calidOK();
      assert m.calidOK();

      assert COK(m.o, m.oHeap);
    }

label HERE:

    assert VHERE: CallOK(m.vs, m.oHeap+m.ns) by {
      assert m.calid();      
      reveal m.calid();
      reveal m.calidOK();
      assert m.calidOK();
      
      assert CallOK(m.vs, m.oHeap+m.ns);
    }

  assert m.calid() by { reveal MCALID; }

  assert VHERX: CallOK(m.vs-{b}, m.oHeap+m.ns) by {
      assert CallOK(m.vs, m.oHeap+m.ns) by { reveal VHERE; }

      CallOKNarrowFocus(m.vs-{b}, m.vs, m.oHeap+m.ns);
      assert CallOK(m.vs-{b}, m.oHeap+m.ns);
    } 

assert CallOK(m.vs-{b}, m.oHeap+m.ns) by { reveal VHERX; }

    assert BHERE: COK(b,  m.oHeap+m.ns);
    assert RHERE: COK(rfv,m.oHeap+m.ns);

    assert b.fields.Keys == oldFields.Keys;

    b.fields := b.fields[n := rfv]; 

    assert b.fields.Keys == oldFields.Keys + {n};

      assert a.fieldModes == old(a.fieldModes);

  assert m.calid() by { reveal MCALID; }

if (b != rfv) {
  assert rfv.fields == old@RHERE(rfv.fields);
  assert rfv.fieldModes == old@RHERE(rfv.fieldModes);
  assert COK(rfv,m.oHeap+m.ns);  

  assert old@BHERE( COK(b,  m.oHeap+m.ns));
  reveal COK();

  assert 
    var a := b;
    var context := m.oHeap+m.ns;
    && (a in context) 
    && (a.AMFO <= context)
    && (forall oo <- a.AMFO :: oo.Ready())
    && (a.Ready() && a.Valid())
    && (a.AllOutgoingReferencesAreOwnership(context))  
    && (a.AllOutgoingReferencesWithinThisHeap(context))
    && (a.AllOwnersAreWithinThisHeap(context));

    assert  COK(b,  m.oHeap+m.ns);
} else {
  assert b == rfv;// gulp!

  assert old@BHERE( COK(b,  m.oHeap+m.ns));
  assert old@RHERE( COK(b,  m.oHeap+m.ns));

  reveal COK(); 
  assert b.fields == old@BHERE(b.fields)[n:=rfv];
  assert b.fieldModes == old@BHERE(b.fieldModes);

  assert 
    var a := b;
    var context := m.oHeap+m.ns;
    && (a in context) 
    && (a.AMFO <= context)
    && (forall oo <- a.AMFO :: oo.Ready())
    && (a.Ready() && a.Valid())
    && (a.AllOutgoingReferencesAreOwnership(context))  
    && (a.AllOutgoingReferencesWithinThisHeap(context))
    && (a.AllOwnersAreWithinThisHeap(context));

  assert COK(b,  m.oHeap+m.ns);
  assert b == rfv;//
  assert COK(rfv,m.oHeap+m.ns); 
}
 
       assert a.fieldModes == old(a.fieldModes);
label DONE:
  assert BDONE: COK(b,  m.oHeap+m.ns);
  assert RDONE: COK(rfv,m.oHeap+m.ns);

  assert m.calid() by { reveal MCALID; }

 assert a.fields.Keys == old(a.fields.Keys);

//     assert m.calid() by
//     {
// 
// //    reveal m.calid(); assert m.calid();
//     reveal m.calidObjects(); assert m.calidObjects();
//     reveal m.calidOK(); assert m.calidOK();
//   
//     reveal m.calidMap(); assert m.calidMap();
//     reveal m.calidSheep(); assert m.calidSheep();
// 
//     reveal COK(); reveal CallOK();
//       
//     }


// assert b.fields.Keys == oldFields.Keys + {n};
// assert mapLEQ(oldFields,b.fields);
// 
//     assert {b} !! m.oHeap;
//     assert CallOK(m.oHeap);
//     assert b in m.ns;
//     assert b !in m.ns-{b};
//     assert b !in onb;
// 
// //    assert unchanged(m.ns - {b});
//     assert unchanged(onb);
//     assert CallOK(onb, ctx);
    assert CallOK(m.ns-{b},m.oHeap+m.ns);
    assert CallOK(m.vs-{b}, m.oHeap+m.ns);

// // // // // // // // // // // // // // // // //
//     assert OldHeapNS2 <= m.oHeap+m.ns;
//     assert FallLEQ(m.oHeap+m.ns);
//     assert COK(b,OldHeapNS2);  
//     COKWiderContext(b,OldHeapNS2, m.oHeap+m.ns - OldHeapNS2);
//     assert (OldHeapNS2 + (m.oHeap+m.ns - OldHeapNS2)) == m.oHeap+m.ns;
//     assert COK(b, m.oHeap+m.ns);
// // // // // // // // // // // // // // // // //
//     assert OldHeapNS2 <= m.oHeap+m.ns;
// //assert FallEQ(m.oHeap+m.ns);
//     assert COK(rfv,OldHeapNS2);
//     COKWiderContext(rfv,OldHeapNS2, m.oHeap+m.ns - OldHeapNS2);
//     assert (OldHeapNS2 + (m.oHeap+m.ns - OldHeapNS2)) == m.oHeap+m.ns;
//     assert COK(rfv, m.oHeap+m.ns);
// // // // // // // // // // // // // // // // //
// 
// assert true by {
//     assert COK(rfv, m.oHeap+m.ns);
//     reveal COK();
//     assert rfv.AllOwnersAreWithinThisHeap(m.oHeap + m.ns);
//     assert rfv.AllOutgoingReferencesAreOwnership(m.oHeap + m.ns);
//     assert rfv.AllOutgoingReferencesWithinThisHeap(m.oHeap + m.ns);
//     assert (rfv in (m.oHeap + m.ns)) ;
//     assert (rfv.AMFO <= (m.oHeap + m.ns));
//     assert (forall oo <- rfv.AMFO :: oo.Ready());
//     assert rfv.Ready();
//     assert (rfv.region.World? || rfv.region.Heap?);
//     assert rfv.OwnersValid();
//     assert rfv.AllFieldsAreDeclared();
//     assert rfv.AllFieldsContentsConsistentWithTheirDeclaration();
//     assert rfv.Valid();
// }
// 
// assert true by {
//     assert COK(b, m.oHeap+m.ns);
//     reveal COK();
//     assert b.AllOwnersAreWithinThisHeap(m.oHeap + m.ns);
//     assert b.AllOutgoingReferencesAreOwnership(m.oHeap + m.ns);
//     assert b.AllOutgoingReferencesWithinThisHeap(m.oHeap + m.ns);
//     assert (b in (m.oHeap + m.ns)) ;
//     assert (b.AMFO <= (m.oHeap + m.ns));
//     assert (forall oo <- b.AMFO :: oo.Ready());
//     assert b.Ready();
//     assert (b.region.World? || b.region.Heap?);
//     assert b.OwnersValid();
//     assert b.AllFieldsAreDeclared();
//     assert b.AllFieldsContentsConsistentWithTheirDeclaration();
//     assert b.Valid();
// }


// // // // // // // // // // // // // // // // // // // 

// assert CallOK((m.m.Values - {b}), m.oHeap+m.ns) by
// {
//   var f := b;
//   var t := rfv;
//   var aa := (m.m.Values - {b});
//   var context := (m.oHeap+m.ns);
//   assert old@HERE(n !in f.fields.Keys);
//   assert    (aa <= context);
//   assert    (f in context);
//   assert     t in context;
//   assert    (n in f.fields.Keys);
//   assert    (f.fields[n] == t);
//   assert old@HERE(CallOK(aa, context));
//   assert old@HERE(COK(f, context));
//   assert     AOK(f,context) ;
//   assert unchanged@HERE(context - {f});
//   
//   AllOKExtraFieldInContext@HERE((m.m.Values - {b}), context, b, n, rfv);
//   assert AllOK(aa, context);
//   CallOKfromAllOK(aa,context);
//   assert CallOK(aa, context);
// }

// // // // // // // // // // // // // // // // // // // 
// 
// label AFTER:
// assert unchanged@HERE(m.m.Values - {b});
// assert unchanged@HERE(m.ns       - {b});
// assert b  in m.m.Values;
// assert b !in m.oHeap;
// 
// 
// assert unchanged@HERE(m.oHeap);
// assert unchanged@HERE(m.oHeap`fields);
// assert unchanged@HERE(m.oHeap`fieldModes);
// assert unchanged@HERE(m.m.Values`fieldModes);
// assert unchanged@HERE((m.m.Values - {b})`fields);
// 
// assert forall h <- m.oHeap :: h.fields     == old@HERE(h.fields);
// assert forall h <- m.oHeap :: h.fieldModes == old@HERE(h.fieldModes);
// 
// assert refOK(b, rfv);
// assert refOK(b, b.fields[n]);


// // // // // // // // // // // // // // // // // // // 

 assert a.fields.Keys == old(a.fields.Keys);

    assert mapLEQ(m'.m,m.m);

 assert unchanged(m'.oHeap);
 assert unchanged(m'.o);
  
    assert CallOK(m'.oHeap);
    assert COK(m'.o, m'.oHeap);
    assert COK(a, m'.oHeap);
    assert COK(b, m'.oHeap+m.ns);
    CallOKfromCOK(b,m.oHeap+m.ns); 

    assert CallOK(m.ns-{b}, m.oHeap+m.ns);
    assert b in m.ns;
    SetMinus3(m.ns,b);
    assert ((m.ns-{b}) + {b}) ==  m.ns;
    CallOKWiderFocus(m.ns-{b},{b},m.oHeap+m.ns);  
    assert CallOK(m.ns,m.oHeap+m.ns);


    reveal m.calid();
    reveal m.calidObjects();
    reveal m.calidOK();
    reveal m.calidMap();
    reveal m.calidSheep();

    assert m.ks == m.m.Keys;
    assert m.vs == m.m.Values;
    assert m.o in  m.oHeap;
    assert m.ks <= m.oHeap;
    assert m.ns !! m.oHeap;
    assert m.vs <= m.ns + m.oHeap;
    assert m.calidObjects();

    assert COK(m'.o, m'.oHeap);
    assert CallOK(m'.oHeap);
    assert CallOK(m.ks, m'.oHeap) by
    {
      reveal m.calidOK();
      assert m.calidOK();
      assert CallOK(m.ks, m.oHeap);
      assert m.oHeap == m'.oHeap;
      assert CallOK(m.ks, m'.oHeap);
    }

    assert CallOK(m.vs, m.oHeap+m.ns) by {

        // assert old@VHERX(CallOK(m.vs-{b}, m.oHeap+m.ns));    
        // assert old@BDONE(COK(b,  m.oHeap+m.ns));
        // assert COK(b,  m.oHeap+m.ns) by { reveal BDONE; }
    assert CallOK(m.vs-{b}, m.oHeap+m.ns);
    assert b in m.vs;
    SetMinus3(m.vs,b);
    assert ((m.vs-{b}) + {b}) ==  m.vs;
    CallOKWiderFocus(m.vs-{b},{b},m.oHeap+m.ns);  
    assert CallOK(m.vs,m.oHeap+m.ns);
    }
    
    assert CallOK(m.ns, m.oHeap+m.ns);
    assert CallOK(m.vs, m.oHeap+m.ns);

    assert m.calidOK();
    assert m.calidMap() by { reveal m.calidOK(); assert m.calidMap(); }

    assert m.calidSheep() by {
        reveal m.calidObjects(); assert m.calidObjects();
        reveal m.calidOK(); assert m.calidOK();

        assert m.ks == m.m.Keys;


        reveal m.AreWeNotMen(); 
        //reveal UniqueMapEntry();
        assert forall x <- m.ks :: m.AreWeNotMen(x, m);
        assert m.calidSheep();
    }

       assert a.fieldModes == old(a.fieldModes);

    assert m.calid();
 assert a.fields.Keys == old(a.fields.Keys);


    // 
    // assert
    //     && m.ks == m.m.Keys
    //     && m.vs == m.m.Values
    //     && m.o in  m.oHeap
    //     && m.ks <= m.oHeap
    //     && m.ns !! m.oHeap
    //     && m.vs <= m.ns + m.oHeap
    // ;

//     assert m.calidObjects();
// 
// 
//         assert COK(m.o, m.oHeap);
//         assert CallOK(m.oHeap);
//         assert CallOK(m.ks, m.oHeap);
//         assert CallOK(m.ns, m.oHeap+m.ns);

// assert  m.calidMap() by 
// {    
//         reveal m.calidObjects(); assert m.calidObjects();
//         reveal m.calidOK(); assert m.calidOK();
//         assert MapOK(m.m); // potentiall should expand this out?
//         assert (forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.m[x] == x)));
//         assert (forall x <- m.ks, oo <- x.AMFO :: m.m[oo] in m.m[x].AMFO);
//         reveal m.calidMap(); assert m.calidMap();
//   }

// bettere off in a contained subscope like above?
//         reveal calidObjects(); assert calidObjects();
//         reveal calidOK(); assert calidOK();
//         assert 
//         && MapOK(m) // potentiall should expand this out?
//         && (forall x <- ks :: (not(inside(x,o)) ==> (m[x] == x)))
//         && (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO)

 assert a.fields.Keys == old(a.fields.Keys);   

  assert n  in a.fields.Keys;
  assert n  in b.fields.Keys;

  assert b.fields.Keys == oldFields.Keys + {n};

 assert b.fields.Keys == old(b.fields.Keys) + {n};
 assert BBN:b.fields.Keys == old(b.fields.Keys) + {n};

 assert (a.fields.Keys - b.fields.Keys) < old(a.fields.Keys - b.fields.Keys);



    reveal m.calidOK(); assert m.calidOK();

    assert m.ks == m.m.Keys;

    reveal m.AreWeNotMen(); 
    assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);

    reveal m.calidSheep(); assert m.calidSheep();

    reveal m.calid(); assert m.calid();

    assert (a.fieldModes == b.fieldModes) by 
     {
      assert a.fieldModes == old(a.fieldModes);
      assert b.fieldModes == old(b.fieldModes);
      reveal FLDMODZ;
      assert old(a.fieldModes) == old(b.fieldModes);
      assert (a.fieldModes == b.fieldModes);
     }

 assert b.fields.Keys == old(b.fields.Keys) + {n} 
    by { reveal BBN; }

assert unchanged(a);

}





lemma SetMinus3(aa : set<Object>, b : Object)
  requires b in aa
  ensures  ((aa - {b}) + {b}) == aa
  {}






//should only bhe called when b is a "new"object not a shared oHeap... 
method {:verify false} {:timeLimit 20} processOneFieldl(a : Object, n : string, b : Object, o : Object, m' : Mapping, os' : set<Object>, oHeap : set<Object>) 
     returns (m : Mapping, os : set<Object>)
//  decreases (oHeap - m'.Keys), a.AMFO
  requires a in oHeap  
  requires a in m'.Keys
  requires b in m'.Values
  requires m'[a] == b
  requires o in oHeap
  requires os' <= oHeap
  requires m'.Values !! oHeap
  requires m'.Keys   <= oHeap

  requires AllOK(oHeap, oHeap)
  requires AllOK(m'.Values, oHeap + m'.Values)
  
  requires AOK(b, oHeap + m'.Values)

  requires  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x))
  requires  m'.Keys !! os' 

  requires n  in a.fields
  requires n !in b.fields
  requires n  in a.fieldModes
  requires n  in b.fieldModes

  requires b.fieldModes[n] == Evil //evilKJX this is actually evil 
                                   //well not *that* evil as I still must satisfy refOK
   
//  requires forall n <- b.fields :: AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);

  //consequently
  requires refOK(a, a.fields[n])
  requires a.region.Heap? == b.region.Heap?
   
  requires MapOK(m')
  ensures  MapOK(m)

  requires os' == oHeap - m'.Keys
  ensures  os  == oHeap - m.Keys

  ensures  os <= os'
  ensures  a in m.Keys
  ensures  m[a] == b
  ensures  b in m.Values

  ensures mapLEQ(m',m)
  
  ensures  AllOK(oHeap, oHeap)
  ensures  AOK(b, oHeap + m.Values)
  ensures  AllOK(m.Values, oHeap + m.Values)

  ensures  forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))

  //ensures  forall x <- m.Keys :: ((x in m'.Keys) || (x in os') && (x !in os))

  ensures m.Keys <= (m'.Keys + os')
  ensures m.Keys !! os

  ensures m.Keys   <= oHeap

  ensures unchanged(a)
  ensures unchanged(oHeap)
  ensures unchanged(m'.Values - {b})

  modifies b`fields
  {
    m  := m';
    os := os';
    assert a in oHeap;
    assert AOK(a,oHeap);
    assert AllOK(oHeap, oHeap);
    assert a.AllFieldsAreDeclared();    
    assert a.AllFieldsContentsConsistentWithTheirDeclaration();
    assert a.AllOutgoingReferencesAreOwnership(oHeap);
    var ofv : Object := a.fields[n];   
    assert AOK(ofv,oHeap);
    assert refOK(a,ofv);
    assert AssignmentCompatible(a, a.fieldModes[n], ofv);

  assert forall n <- b.fields :: AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
    assert b.fieldModes[n] == Evil;

    print "procF  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
    print "procF    (recurse on field ",n,")\n";

    // arseume a in oHeap;
    // arseume o in oHeap;
    // arseume os' <= oHeap;
    // arseume AllOK(oHeap, oHeap);
    // arseume AllOK(m'.Values, oHeap + m'.Values);
    // arseume forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
    // arseume m'.Keys !! os' ;

assert AllOK(m'.Values, oHeap + m'.Values);

assert AllOK(m.Values, oHeap + m.Values);

// // // // // // // // // // // // // // // // // // // // // // // // // 


  assert ofv in oHeap;
  assert o in oHeap;
  assert os <= oHeap;

  assert AllOK(oHeap, oHeap);
  assert AllOK(m.Values, oHeap + m.Values);

  assert  forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
  assert  m.Keys !! os ;

  assert os == oHeap - m.Keys;

  assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys;
  assert forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?;
  assert forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner ;
  assert forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO;



// // // // // // // // // // // // // // // // // // // // // // // // // 

var rfv, rm, ros := walkiesClean(ofv, o, m, os, oHeap);

assert ofv in rm.Keys;
assert rm[ofv] == rfv;
assert AllOK(oHeap, oHeap);

//DO WE NEED TO TRACK IF THE  is SHARED vs COPIED..
//can we assme this method is only called on COPIED OBJEXTS --- YES
//so don't need to distinguish if it's copied... 

//assert AllOK(m'.Values, oHeap + m'.Values);   //would need unchanged shit..


assert AllOK(rm.Values, oHeap + rm.Values);

label THERE:

assert AllOK(rm.Values, oHeap + rm.Values);
assert AllOK(oHeap, oHeap);

        assert rfv in oHeap + rm.Values;
        assert AOK(rfv, oHeap + rm.Values);

        // assert rm[a.fields[n]] == rfv;

        // assert forall oo <- ofv.AMFO :: rm[ofv] in rfv.AMFO;

//establish that ofv's ownership structure
//is paralleled by rfv's ownership structure

  assert a in rm.Keys;
  assert forall x <- rm.Keys | x.region.Heap? :: x.region.owner in rm.Keys;
  assert forall x <- rm.Keys :: x.region.World? == rm[x].region.World?;
  assert forall x <- rm.Keys, oo <- x.AMFO :: oo in rm.Keys;
  assert forall x <- rm.Keys, oo <- x.AMFO :: rm[oo] in rm[x].AMFO;
  assert forall x <- rm.Keys |  x.region.Heap? ::
       (rm[x].region.Heap?)  &&
       (rm[x.region.owner] == rm[x].region.owner);

//extra bit because I'm a bit dumb
if (ofv.region.Heap?) {
    assert rfv.region.Heap?;
    assert ofv in oHeap;
    assert ofv.region.owner in oHeap;
    assert ofv in rm.Keys;
    assert ofv.region.owner in rm.Keys;
    assert rm[ofv].region.owner == rfv.region.owner;
    assert rm[ofv.region.owner] == rfv.region.owner;
    assert forall x <- rm.Keys, oo <- x.AMFO :: rm[oo] in rm[x].AMFO; //FROM ABOVE
    assert forall oo <- a.AMFO :: rm[oo] in rm[a].AMFO;
    assert forall oo <- ({a}) :: rm[oo] in ({rm[a]});
    assert forall oo <- (a.AMFO + {a}) :: rm[oo] in (rm[a].AMFO + {rm[a]});
    assert rm[a] == b;
    assert rm[a].AMFO == b.AMFO;
    assert (rm[a].AMFO + {rm[a]}) == (b.AMFO + {b});
   // assert forall oo <- (a.AMFO + {a}) :: rm[oo] in (b.AMFO + {b});


    assert inside(a,ofv.region.owner);
    assert ofv.region.owner == a || ofv.region.owner in a.AMFO;
    assert ofv.region.owner in (a.AMFO + {a});
    assert rfv.region.owner in (b.AMFO + {b});
    assert inside(b,rfv.region.owner);
    assert refOK(b, rfv);
} else {
    assert ofv.region.World?;
    assert rfv.region.World?;
    assert refOK(b, rfv);
}
  
  assert refOK(b, rfv);
//  assert refOK(b, b.fields[n]);  oops not done yet!

  assert AllOK(oHeap, oHeap);



  assert AOK(b, oHeap + m.Values);
  assert b.AllOutgoingReferencesAreOwnership(oHeap+m.Values);
  assert b.AllOutgoingReferencesWithinThisHeap(oHeap+m.Values);

  assert forall n <- b.fields.Keys:: refOK(b, b.fields[n]);
  assert b.outgoing() <= oHeap+m.Values;

        m := rm;

assert AllOK(oHeap, oHeap);
assert AllOK(m.Values, oHeap + m.Values);

        label HERE:


assert AllOK(oHeap, oHeap);
assert blurk: AllOK(oHeap, oHeap);
assert blurk2: forall x <- oHeap :: AOK(x, oHeap);
assert forall h <- oHeap :: AOK(h,oHeap);

assert AllOK(m.Values, oHeap + m.Values);
assert bfucker: AllOK(m.Values - {b}, oHeap + m.Values);

assert AllOK(m.Values- {b}, oHeap + m.Values);

        var oldFields := b.fields;
        assert oldFields == b.fields == old(b.fields);
        var oldHeapMValues := oHeap + m.Values;

        b.fields := b.fields[n := rfv]; 

label AFTER:
assert unchanged@HERE(m.Values - {b});
assert b  in m.Values;
assert b !in oHeap;

assert unchanged@HERE(oHeap);
assert unchanged@HERE(oHeap`fields);
assert unchanged@HERE(oHeap`fieldModes);
assert unchanged@HERE(m.Values`fieldModes);
assert unchanged@HERE((m.Values - {b})`fields);

assert forall h <- oHeap :: h.fields     == old@HERE(h.fields);
assert forall h <- oHeap :: h.fieldModes == old@HERE(h.fieldModes);



assert AllOK(oHeap, oHeap) by {
  AllOKtardis@HERE(oHeap, oHeap);
assert unchanged@HERE(oHeap`fields);
assert unchanged@HERE(oHeap`fieldModes);
  assert unchanged@HERE(oHeap);
  reveal blurk; }

assert old@HERE(AllOK(m.Values - {b}, oHeap + m.Values)) by { reveal bfucker; }


        assert rfv == b.fields[n];
        assert mapLEQ(oldFields, b.fields);

        assert oldFields[n:=rfv] == b.fields;

        assert forall h <- m.Values :: (h != b) ==> h.fields == old@THERE(h.fields);
        assert forall h <- (m.Values - {b}) :: h.fields == old@THERE(h.fields);
        assert forall h <- (m.Values - {b}) :: h.fieldModes == old@THERE(h.fieldModes);

//         assert AllOK(m.Values - {b}, oHeap + m.Values) by 
//         {    
//           assert unchanged@HERE(m.Values - {b});
//           assert old@HERE(AllOK(m.Values - {b}, oHeap + m.Values)) by { reveal bfucker; }
//    assert unchanged@HERE(m.Values - {b});
//    assert unchanged@HERE(oHeap);
//       assert unchanged@HERE( oHeap + m.Values - {b} );
// //KJX WONT PROVE IS ACTUALLY WRONG           AllOKtardis@HERE(m.Values - {b}, oHeap + m.Values);

// assert  AllOK(m.Values - {b}, oHeap + m.Values);
           
//            }

        assert forall h <- (m.Values - {b}) :: old@HERE(AOK(h, oHeap + m.Values));
        assert forall m <- b.fields.Keys :: (m != n) ==> b.fields[m] == old@THERE(b.fields[m]);

        //assert forall h <- (m.Values - {b}) :: AOK(h, unchanged@HERE(oHeap+m.Values));


          assert n   !in oldFields.Keys;
        //can't use MappingPlusOneKeyValue because two fields can point to the same object!
        // assert MappingPlusOneKeyValue(oldFields,n,rfv) == b.fields;

 assert refOK(b, rfv);
 assert refOK(b, b.fields[n]);

  assert oldHeapMValues == oHeap + m.Values;
  assert unchanged@HERE( oHeap + m.Values - {b} ); 
  //        assert AllOK(m.Values - {b}, oHeap+m.Values );  //doean work cos B has changed...
  assert old@HERE(AOK(b, oHeap + m.Values));

  assert forall n <- old@HERE(b.fields.Keys) :: refOK(b, b.fields[n]);
  assert old@HERE(b.outgoing()) <= oHeap+m.Values;

  assert rfv in oHeap+m.Values;
  assert b.fields[n]  in oHeap+m.Values;
  assert b.outgoing() <= oHeap+m.Values;
  assert b.AllOutgoingReferencesWithinThisHeap(oHeap+m.Values);

  assert forall m <- old@HERE(b.fields.Keys) :: refOK(b, b.fields[m]);
  assert refOK(b,b.fields[n]);
  assert forall m <- old@HERE(b.fields.Keys) + {n} :: refOK(b, b.fields[m]);
  assert old@HERE(b.fields.Keys) + {n} == b.fields.Keys;
  assert forall m <- b.fields.Keys :: refOK(b, b.fields[m]);
  assert b.AllOutgoingReferencesAreOwnership(oHeap+m.Values);

  assert rfv in oHeap+m.Values;

  assert old@HERE(forall n <- b.fields :: AssignmentCompatible(b, b.fieldModes[n], b.fields[n]));
  assert forall n <- old@HERE(b.fields) :: AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
  assert refOK(b,b.fields[n]);


  // match (a.fieldModes[n]) {
  //   case Evil =>  assert AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);

  //   case Rep | Owned(_) | Loaned(_) => 
  //       assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
  //       assert ofv == a.fields[n];
  //       assert ofv.region.Heap?;
  //       assert ofv.region.owner == a;
  //       assert rfv == b.fields[n];
  //       assert rfv.region.Heap?;
  //       assert b == rm[a];
  //       assert rfv == rm[ofv];
  //       assert b == rfv.region.owner;
  //       assert b == rm[a.fields[n].region.owner];
  //       assert b == b.fields[n].region.owner;
  //       assert AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);

  //   case Peer =>
  //       assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
  //       assert a.region == a.fields[n].region;
  //       if a.region.Heap? {
  //         assert b.region.Heap?;
  //         assert rm[a.region.owner] == rm[a.fields[n].region.owner];
  //         assert rm[a].region.owner == rm[a].fields[n].region.owner;
  //         assert b.region.owner     == b.fields[n].region.owner;
  //       } else {
  //         assert a.region.World?;
  //         assert b.region.World?;
  //       }
  //       assert b.region == b.fields[n].region;
  //       assert AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);

  //   case Borrow(pp,bb,nn,ff) => 
  //       assert AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);
  //       assert refOK(a,a.fields[n]);
  //       assert refOK(b,b.fields[n]);
  //       assert AssignmentCompatible(b, b.fieldModes[n], b.fields[n]);
  //    }

        os := ros;
        m  := rm;

assert b.OwnersValid();
assert b.AllFieldsAreDeclared();
assert b.AllFieldsContentsConsistentWithTheirDeclaration();

        assert b.Valid() && b.TRUMP();

  assert old@THERE(AllOK(oHeap, oHeap));
  assert forall h <- oHeap:: old@THERE(AOK(h, oHeap));
  assert unchanged@THERE(oHeap, oHeap`fields, oHeap`fieldModes);
  assert forall h <- oHeap :: h.fields == old@THERE(h.fields);
  assert forall h <- oHeap :: h.fieldModes == old@THERE(h.fieldModes);
  assert AllOK(oHeap, oHeap);

  label BOK:
  assert AOK(b, oHeap + m.Values);
 
  assert old(AllOK(m'.Values, oHeap + m'.Values));
  assert old@THERE(AllOK(rm.Values, oHeap + rm.Values));
  assert old@HERE(AllOK(rm.Values, oHeap + rm.Values));
  assert unchanged@THERE(oHeap, oHeap`fields, oHeap`fieldModes);

  //assert old@HERE(forall h <- (oHeap + rm.Values) :: AOK(h, oHeap + rm.Values));
  assert old@HERE(forall h <- (rm.Values) :: AOK(h, oHeap + rm.Values));
  assert rm == m;
  assert old@HERE(forall h <- (m.Values) :: AOK(h, oHeap + m.Values));

  assert AOK(b, (oHeap + m.Values));
  assert AllOK(oHeap, oHeap);

/// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// 
///precoonditions for AllOKExtraFieldInContext
{
  var f := b;
  var t := rfv;
  var aa := (m.Values - {b});
  var context := (oHeap + m.Values);
  assert old@HERE(n !in f.fields.Keys);
  assert    (aa <= context);
  assert    (f in context);
  assert     t in context;
  assert    (n in f.fields.Keys);
  assert    (f.fields[n] == t);
  assert old@HERE(AllOK(aa, context));
  assert old@HERE(AOK(f, context));
  assert     AOK(f,context) ;
  assert unchanged@HERE(context - {f});
  }
  AllOKExtraFieldInContext@HERE((m.Values - {b}), (oHeap + m.Values), b, n, rfv);
/// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// 

  assert AllOK(m.Values - {b}, (oHeap + m.Values));


  // forall h <- m.Values ensures AOK(h, oHeap+m.Values) {
  //   if (h == b) { assert old@BOK(AOK(b, oHeap+m.Values));
  //                 assert unchanged@BOK(b, oHeap+m.Values);
  //                }
  //     else {
  //       assert h != b;
  //       assert old@HERE(AOK(h, oHeap+m.Values));

  //       assert unchanged@HERE(h);
  //       assert unchanged@HERE(oHeap);
  //       assert h.fields     == old@HERE(h.fields);
  //       assert h.fields.Keys     == old@HERE(h.fields.Keys);
  //       assert h.fields.Values     == old@HERE(h.fields.Values);

  //       assert h.fieldModes == old@HERE(h.fieldModes);


  //       assert AOK(h, oHeap + m.Values);
  //     }
    
  // }

  assert forall h <- (m.Values - {b}) :: AOK(h, oHeap + m.Values);
  assert AOK(b, oHeap + m.Values);
  assert m.Values - {b} + {b} == m.Values;
  assert forall h <- (m.Values) :: AOK(h, oHeap + m.Values);
  assert AllOK(m.Values, oHeap + m.Values);

  assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
  assert m.Keys <= (m'.Keys + os');
  assert m.Keys !! os;
  assert mapLEQ(m',m);


}


method skip() modifies {} {}

// method processAllFieldz(a : Object, b : Object, o : Object, m' : Mapping, os' : set<Object>, oHeap : set<Object>) 
//      returns (m : Mapping, os : set<Object>)

//  decreases os'
//   requires a in oHeap
//   requires o in oHeap
//   requires os' <= oHeap

//   requires AllOK(oHeap, oHeap)
//   requires AllOK(m'.Values, oHeap + m'.Values)
  
//   requires  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x))
//   requires  m'.Keys !! os' 

//     // assert a in oHeap;
//     // assert o in oHeap;
//     // assert os' <= oHeap;
//     // assert AllOK(oHeap, oHeap);
//     // assert AllOK(m'.Values, oHeap + m'.Values);
//     // assert  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
//     // assert  m'.Keys !! os' ;



//   ensures  os <= os'
//   // ensures  b in (oHeap + m.Values)

//   ensures mapLEQ(m',m)
  
//   ensures  AllOK(oHeap, oHeap)
//   ensures  AOK(b, oHeap + m.Values)
//   ensures  AllOK(m.Values, oHeap + m.Values)

//   ensures  forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))

//   //ensures  forall x <- m.Keys :: ((x in m'.Keys) || (x in os') && (x !in os))

//   ensures m.Keys <= (m'.Keys + os')
//   ensures m.Keys !! os
// {
//   for i := 0 to |ns|
//      invariant os <= os' - {a}
//      invariant b.Valid() && b.TRUMP()
//      invariant mapLEQ(m',m)
//      invariant a in oHeap
//      invariant o in oHeap
//      invariant os' <= oHeap
//      invariant AllOK(oHeap, oHeap)
//      invariant AllOK(m'.Values, oHeap + m'.Values)
//      invariant  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x))
//      invariant  m'.Keys !! os' 
//    {
//         var n : string := ns[i];
//         var ofv : Object := a.fields[n];   
//     print "  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
//     print "    (recurse on field ",n,")\n";

//     arseume a in oHeap;
//     arseume o in oHeap;
//     arseume os' <= oHeap;
//     arseume AllOK(oHeap, oHeap);
//     arseume AllOK(m'.Values, oHeap + m'.Values);
//     arseume forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
//     arseume m'.Keys !! os' ;

//     arseume os <= os' - {a};





//         var rfv, rm, ros := walkiesClean(ofv, o, m, os, oHeap);

//         assert rfv in rm.Values;
//         arseume rfv.AMFO <= rm.Values;

//         assert m[a.fields[n]] == rfv;

//         assert forall oo <- ofv.AMFO :: rm[ofv] in rfv.AMFO;

//         if (rfv.region.Heap?) 
//         {
//           assert AOK(a,oHeap);
//           assert a.AllOutgoingReferencesAreOwnership(oHeap);
//           assert refOK(a,ofv);
//           assert inside(a,ofv.region.owner);
//           assert || ofv == a
//                  || a in ofv.region.owner.AMFO;

// //HERE
//           assert inside(a,ofv.region.owner);

//           assert inside(b, rfv.region.owner);
//           assert refOK(b, rfv);
//         } else {
//           assert rfv.region.World?;
//           assert refOK(b, rfv);
//         }

//         assert refOK(b, rfv);

//         label HERE:

//         b.fields := b.fields[n := rfv]; //  MOVED

//         assert unchanged@HERE( oHeap - {b} );
//         assert AllOK(oHeap - {b}, oHeap );

//         assert refOK(b, rfv);


//         os := ros;
//         m  := rm;



//         assert b.Valid() && b.TRUMP();

//   assert AllOK(oHeap, oHeap);
//   assert AOK(b, oHeap + m.Values);
//   assert AllOK(m.Values, oHeap + m.Values);
//   assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
//   assert m.Keys <= (m'.Keys + os');
//   assert m.Keys !! os;
//   assert mapLEQ(m',m);


//    }
//      print "RETN walkiesClean done ", fmtobj(a), " ", |os|, "\n";


//     assert b.Valid() && b.TRUMP();

//   assert AllOK(oHeap, oHeap);
//   assert AOK(b, oHeap + m.Values);
//   assert AllOK(m.Values, oHeap + m.Values);
//   assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
//   assert m.Keys <= (m'.Keys + os');
//   assert m.Keys !! os;
//   assert mapLEQ(m',m);


// }




///////////////// big htoup of AOK methods that shojld eventuall go away 


twostate lemma {:onlyAAKE} AOKtardis(o : Object, context : set<Object>)
   requires old(AOK(o, context))
   requires unchanged(o)
   requires unchanged(context)
   ensures  AOK(o, context)
{}


twostate lemma {:onlyAAKE} AllOKtardis(aa : set<Object>, context : set<Object>)
   requires old(AllOK(aa, context))
   requires unchanged(aa)
   requires unchanged(context)
   ensures  AllOK(aa, context)
{}

twostate lemma {:onlyAAKE} SubsetUnchangedCovariant(less : set<Object>, more : set<Object>)
  requires less <= more
  requires unchanged(more)
  ensures  unchanged(less)
 {}

twostate lemma {:onlyAAKE} AllOKtardisSubset(less : set<Object>, more : set<Object>,
                                             lessContext : set<Object>, moreContext : set<Object>)
  requires old(AllOK(less,lessContext))
  requires less <= more
  requires lessContext <= moreContext
  requires unchanged(more)
  requires unchanged(moreContext)
  ensures  unchanged(less)
  ensures  unchanged(lessContext)
  ensures  AllOK(less, lessContext)
 {}



twostate lemma {:onlyAAKE} AOKExtraFieldInContext(a : Object, context : set<Object>,
                  f : Object, n : string, t : Object) 
  requires old(n !in f.fields.Keys)

  requires    (a in context)
  requires    (f in context)
  requires     t in context
  requires    (n in f.fields.Keys)
  requires    (f.fields[n] == t)

  requires old(AOK(a, context))
  requires old(AOK(f, context))
  requires     AOK(f,context) 
  requires unchanged(context - {f})
  ensures  AOK(a, context)
{}


twostate lemma {:onlAAKEy} AllOKExtraFieldInContext(aa : set<Object>, context : set<Object>,
                  f : Object, n : string, t : Object) 
  requires old(n !in f.fields.Keys)

  requires    (aa <= context) 
  requires    (f in context)
  requires     t in context
  requires    (n in f.fields.Keys)
  requires    (f.fields[n] == t)

  requires old(AllOK(aa, context))
  requires old(AOK(f, context))
  requires     AOK(f,context) 
  requires unchanged(context - {f})
  ensures  AllOK(aa, context)
{
  forall  a <- aa { AOKExtraFieldInContext(a, context, f, n, t); }
   assert forall a <- aa ::  AllOK(aa, context);
}




lemma {:onlyAKE} AOKWiderContext(a : Object, context : set<Object>, extra : set<Object>) 
  requires a in context
  requires AOK(a,context)
  ensures AOK(a,context + extra)
{}

lemma {:onlyAKE} AllOKWiderContext(aa: set<Object>, context : set<Object>, extra : set<Object>) 
  requires aa <= context
  requires AllOK(aa,context)
  ensures AllOK(aa,context + extra)
{ 
  forall a <- aa { AOKWiderContext(a,context,extra); }
}


lemma {:onlyAKE} AllOKWiderFocus(aa: set<Object>, bb : set<Object>, context : set<Object>) 
  requires aa <= context
  requires bb <= context
  requires AllOK(aa,context)
  requires AllOK(bb,context)
  ensures  AllOK(aa+bb,context)
{ 
  assert forall a <- (aa     ) :: AOK(a,context);
  assert forall a <- (     bb) :: AOK(a,context);
  assert forall a <- (aa + bb) :: AOK(a,context);
}


lemma {:onlyAAKE} AOKAMFO(a : Object, context : set<Object>) 
  decreases a.AMFO
  requires  AOK(a, context)
  requires  AllOK(context)
  ensures   AllOK({a}+a.AMFO, context)
{} 

///IF owners OK were also bounded by a (sub)heap, then 
///the reads clauses could just look over that whole subheap...
///that way lies... seplogic?
predicate {:onlyAKE} AOK(a : Object, context : set<Object>)
   decreases a.AMFO
     reads context`fields, context`fieldModes
  // reads (set o1 <- context, o2 <- o1.ValidReadSet() :: o2)`fields
  // reads (set o1 <- context, o2 <- o1.ValidReadSet() :: o2)`fieldModes
 {
    && (a in context) 
    && (a.AMFO <= context)
    && (forall oo <- a.AMFO :: oo.Ready())
    && (a.TRUMP()||(a.Ready() && a.Valid()))
    && (a.AllOutgoingReferencesAreOwnership(context))  
    && (a.AllOutgoingReferencesWithinThisHeap(context))
    && (a.AllOwnersAreWithinThisHeap(context))
}

lemma {:onlyAKE} ValidReadSetIsOKToo(a : Object, context : set<Object> )
  requires AOK(a, context)
  requires AllOK(context, context)
  ensures  a.ValidReadSet() <= context
  {
    assert AOK(a, context);
    assert a in context;
    assert a.fields.Values <= context;
    assert a.AMFO <= context;
    assert (set o1 <- a.AMFO, o2 <- o1.fields.Values :: o2) <= context;
  }


predicate {:onlyNUKE} AllOK(aa :set<Object>, context : set<Object> := aa)
  // reads (set o1 <- context, o2 <- o1.ValidReadSet() :: o2)`fields
  // reads (set o1 <- context, o2 <- o1.ValidReadSet() :: o2)`fieldModes
  reads context`fields, context`fieldModes
{  
forall a <- aa :: AOK(a,context)
}


predicate {:onlyFEQ} FEQ(a : Object, b : Object) 
 reads a`fields, b`fields, a`fieldModes, b`fieldModes
{
  (a.fields == b.fields) && (a.fieldModes == b.fieldModes)
}

predicate {:onlyFEQ} FLEQ(a : Object, b : Object) 
 reads a`fields, b`fields, a`fieldModes, b`fieldModes
{
  mapLEQ(a.fields,b.fields) && mapLEQ(a.fieldModes,b.fieldModes)
}

twostate predicate {:onlyFEQ} FallEQ(aa : set<Object>) 
reads aa`fields, aa`fieldModes
{
  forall a <- aa :: (a.fields == old(a.fields)) && (a.fieldModes == old(a.fieldModes))
}

// twostate predicate {:onlyFEQ} FallLEQ(new aa : set<Object>)
// reads aa`fields, aa`fieldModes
// {
//   forall a <- aa | old(allocated(a)) :: FLEQ(old(a),a)
// }


twostate lemma {:onlyFEQ} FallUnchanged(aa : set<Object>)
  requires unchanged(aa)
  ensures  FallEQ(aa)
{
}


///opaque versions for "cake" constructor

method {:onlyMashed} CallOKMashed(uu : set<Object>, aa :set<Object>, context : set<Object>)
   requires CallOK(aa,context)
   requires uu <= aa <= context
   modifies aa - uu
   ensures unchanged(uu)

{
   modify aa - uu;
   assert unchanged(uu);

   reveal CallOK(), COK();

   assert CallOK(uu,context);
}




// 
// twostate lemma {:onlyCall} CallOKUpdated(a : object, new aa : set<Object>, new context : set <Object>)
//   requires forall x <- aa | old(allocated(x)) :: old(COK(x, context))
//   requires unchanged(aa - {a})
//   requires unchanged(context - {a})
//   requires ANOW: COK(a,context)
//   ensures  CallOK(aa, context)
// {
//   reveal CallOK(), COK();
// 
//   assert CallOK(aa, context) by {
//     forall x <- aa ensures COK(x, context) {
//       if (x != a) {
//         assert old(COK(x,context));
//         assert unchanged(x) by {
//           assert unchanged(aa - {a});
//           assert x in aa;
//           assert x != a;
//           assert x in (aa - {a});
//           assert unchanged(x);
//         }
//         assert COK(x,context);
//       } else {
//         assert COK(a,context) by { reveal ANOW; }
//         assert x == a;
//         assert COK(x,context);
//       }
//  
//     }
//   } 
// }


lemma {:onlyNUKE} AOKfromCOK(a : Object, context : set<Object>) 
  requires COK(a, context)
  ensures  AOK(a, context)
{
  reveal COK();
}


lemma {:onlyNUKE} COKfromAOK(a : Object, context : set<Object>) 
  requires AOK(a, context)
  ensures  COK(a, context)
{
  reveal COK();
}

lemma {:onlyNUKE} CallOKfromAllOK(aa :set<Object>, context : set<Object> := aa) 
  requires  AllOK(aa, context)
   ensures  CallOK(aa, context)
{
  reveal CallOK(), COK();
  assert forall a <- aa :: AOK(a, context);
  forall a <- aa  ensures (CallOK(aa,context))
     { assert AOK(a, context);
      COKfromAOK(a, context);
      assert COK(a, context); }
  assert  CallOK(aa, context);
}



lemma AllOKfromCallOK(aa :set<Object>, context : set<Object> := aa) 
  requires CallOK(aa, context)
  ensures   AllOK(aa, context)
{
  reveal CallOK(); reveal COK();
  assert forall a <- aa :: COK(a, context);
  forall a <- aa  ensures (AllOK(aa,context))
     { AOKfromCOK(a, context); assert AOK(a, context); }
  assert forall a <- aa :: AOK(a,context);
  assert   AllOK(aa, context);
}


//  requires  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x))



predicate MapOKLEQ(left : Map, right : Map)
  reads left.oHeap`fields,  left.oHeap`fieldModes
  reads left.ns`fields,     left.ns`fieldModes
  reads right.oHeap`fields, right.oHeap`fieldModes
  reads right.ns`fields,    right.ns`fieldModes
  requires left.calid()
  requires right.calid()
  {
    reveal left.calid();
    reveal right.calid();
    assert left.calidObjects();
    assert right.calidObjects();
    && left.ks <= right.ks
    && left.vs <= left.vs
    && mapLEQ(left.m, right.m)
  }


// predicate {:onlyAndTheRest} MapOKAndTheRest(m : Mapping, rest : set<Object>)
// {
//   && (forall x <- m.Keys, oo <- x.AMFO :: oo in (m.Keys+rest))
//   && (forall x <- m.Keys, oo <- x.AMFO :: 
//       || (oo in rest)
//       || (oo in m.Keys))

//   && (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?)
//   && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
//   && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in (m.Keys+rest))
//   && (forall x <- m.Keys |  x.region.Heap? ::
//        || (x.region.owner in rest)
//        || (m[x.region.owner] == m[x].region.owner))
//   && (forall x <- m.Keys, oo <- x.AMFO :: 
//        || (oo in rest)
//        || (m[oo] in m[x].AMFO))
// //  && forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))
// }


 
//{:timeLimit 30} 

method {:verify false} walkiesClean(a : Object, o : Object, m' : Mapping, os' : set<Object>, oHeap : set<Object>) 
      returns (b : Object, m : Mapping, os : set<Object>)
//  decreases (oHeap - m'.Keys)
//  decreases os'
  decreases (oHeap - m'.Keys), a.AMFO

  requires a in oHeap
  requires o in oHeap
  requires os' <= oHeap

  requires AOK(a, oHeap)
  requires AOK(o, oHeap)
  requires AllOK(oHeap)
  requires AllOK(m'.Keys, oHeap)
  requires AllOK(m'.Values, oHeap+m'.Values)


  requires m'.Keys !! os'
  requires forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x))
  requires forall x <- m'.Keys, oo <- x.AMFO :: oo in m'.Keys && m'[oo] in m'[x].AMFO
   
  requires forall x <- m'.Keys :: 
     if (inside(x,o))
       then ((m'[x] !in oHeap) && (UniqueMapEntry(m',x))) 
       else (m'[x] == x)

  // KJX shojld be provable but haven't pusjed it
  //deletinf this gets 10more timeouts
  requires os' == oHeap - m'.Keys
  ensures  os  == oHeap - m.Keys

  requires m'.Keys <= oHeap
  ensures  m.Keys  <= oHeap


    // assert a in oHeap;
    // assert o in oHeap;
    // assert os' <= oHeap;
    // assert AllOK(oHeap, oHeap);
    // assert AllOK(m'.Values, oHeap + m'.Values);
    // assert  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
    // assert  m'.Keys !! os' ;


  requires MapOK(m')
  ensures  a.region.Heap? == b.region.Heap?


  ensures MapOK(m)


  ensures  os <= os'
  // ensures  b in (oHeap + m.Values)  /// see below!

  ensures mapLEQ(m',m)

  ensures  AOK(b, oHeap+m.Values)
  ensures  AllOK(oHeap)
  ensures  AllOK(m.Keys, oHeap)
  ensures  AllOK(m.Values, oHeap+m.Values)

  ensures  forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))
  ensures  forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO

  ensures  forall x <- m.Keys :: 
     if (inside(x,o))
       then ((m[x] !in oHeap) && (UniqueMapEntry(m,x))) 
       else (m[x] == x)

  //ensures  forall x <- m.Keys :: ((x in m'.Keys) || (x in os') && (x !in os))

//  ensures m.Keys <= (m'.Keys + os')
//    means thesame as enures m.Keys <= (m'.Keys + oHeap - m.Keys)
// mnore or less m.Keys <= oHep && mapLEQ(m',m),,.

  ensures m.Keys !! os
  //ensures (a in m.Keys) ==> (m[a] == b)  //mmmKJX - yes if we canstop to stupid
  ensures a in m.Keys
  ensures (m[a] == b) 
//  ensures b in m.Values
  ensures  b in (oHeap + m.Values)

   //mmmKJX - careful here,e need to get rid ot he other case
   //  (if we can get rid of the "os in proces" case, we can go to m[a] == b without the guard

  //assertions versions, for use when hacking
  // assert AllOK(oHeap, oHeap);
  // assert AOK(b, oHeap + m.Values);
  // assert AllOK(m.Values, oHeap + m.Values);
  // assert m.Keys <= (m'.Keys + os');
  // assert m.Keys !! os;


// method {:timeLimit 5} walkiesClean(a : Object, o : Object, m' : Mapping, os' : set<Object>, oHeap : set<Object>) 
//      returns (b : Object, m : Mapping, os : set<Object>)
//   decreases os'
//   requires a in oHeap
//   requires o in oHeap
//   requires os' <= oHeap

//   requires AllOK(oHeap, oHeap)
//   requires AllOK(m'.Values, oHeap + m'.Values)
  
//   requires  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x))
//   requires  m'.Keys !! os' 

//     // assert a in oHeap;
//     // assert o in oHeap;
//     // assert os' <= oHeap;
//     // assert AllOK(oHeap, oHeap);
//     // assert AllOK(m'.Values, oHeap + m'.Values);
//     // assert  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
//     // assert  m'.Keys !! os' ;



//   ensures  os <= os'
//   // ensures  b in (oHeap + m.Values)

//   ensures mapLEQ(m',m)
  
//   ensures  AllOK(oHeap, oHeap)
//   ensures  AOK(b, oHeap + m.Values)
//   ensures  AllOK(m.Values, oHeap + m.Values)

//   ensures  forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))

//   //ensures  forall x <- m.Keys :: ((x in m'.Keys) || (x in os') && (x !in os))

//   ensures m.Keys <= (m'.Keys + os')
//   ensures m.Keys !! os

//   //assertions versions, for use when hacking
//   // assert AllOK(oHeap, oHeap);
//   // assert AOK(b, oHeap + m.Values);
//   // assert AllOK(m.Values, oHeap + m.Values);
//   // assert m.Keys <= (m'.Keys + os');
//   // assert m.Keys !! os;

{

//KJX FROM HERE
  assert AllOK(m'.Values, oHeap + m'.Values);


  os := os';
  m  := m';
  b := a; 
//////CONSIDER s/m'/m/ ...

  assert os  == oHeap - m.Keys;


//getting around a stiupd bug..
//assert AllOK(m.Values, oHeap+m.Values);  /// BREAKS WTF

  assert  MAPOK0: AllOK(m.Values, oHeap+m.Values) by { 
    assert unchanged(m'.Values);
    assert unchanged(oHeap+m'.Values);
    assert AllOK(m'.Values, oHeap + m'.Values);
    assert m == m';
    assert m.Keys == m'.Keys;
    assert m.Values == m'.Values;
    assert oHeap+m.Values == oHeap+m'.Values;
    assert unchanged(m.Values);
    assert unchanged(oHeap+m.Values);
    assert forall x <- m'.Values :: AOK(x,oHeap+m'.Values);
    assert forall x <- m.Values :: AOK(x,oHeap+m.Values);
    
    assert AllOK(m.Values, oHeap+m.Values);
   }

  assert AllOK(m.Values, oHeap+m.Values) by { reveal MAPOK0; }


//note stuff isn't in here...

  // assert 
  //   && (a in oHeap) 
  //   && (a.TRUMP() && a.Valid())
  //   && (a.AllOutgoingReferencesAreOwnership(oHeap))  
  //   && (a.AllOutgoingReferencesWithinThisHeap(oHeap))
  //   && (a.AllOwnersAreWithinThisHeap(oHeap));



  // assert forall o <- oHeap     :: o.TRUMP() && o.Valid();
  // assert forall o <- m'.Values :: o.TRUMP() && o.Valid();
  // assert forall o <- (oHeap) :: (o.AllOutgoingReferencesAreOwnership(oHeap));
  // assert forall o <- (oHeap) :: (o.AllOutgoingReferencesWithinThisHeap(oHeap));
  // assert forall o <- (oHeap) :: (o.AllOwnersAreWithinThisHeap(oHeap));
  // assert forall o <- (m'.Values) :: (o.AllOutgoingReferencesAreOwnership(oHeap + m'.Values));
  // assert forall o <- (m'.Values) :: (o.AllOutgoingReferencesWithinThisHeap(oHeap + m'.Values));
  // assert forall o <- (m'.Values) :: (o.AllOwnersAreWithinThisHeap(oHeap + m'.Values));

  assert AOK(a, oHeap);

  assert AOK: AOK(a, oHeap);
  assert HOK: AllOK(oHeap, oHeap);
  assert KOK: AllOK(m'.Keys, oHeap); // owners must all be in Keys, but, fields can point out.
  assert VOK: AllOK(m'.Values, oHeap+m'.Values);

  assert KAMFOK: forall x <- m'.Keys, oo <- x.AMFO :: oo in m'.Keys && m'[oo] in m'[x].AMFO;
    
  assert forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
  
  assert forall x <- m'.Keys :: 
     if (inside(x,o))
       then ((m'[x] !in oHeap) && (UniqueMapEntry(m',x))) 
       else (m'[x] == x);


  assert os' == oHeap - m'.Keys;
  assert os  == oHeap - m.Keys;

  // assert m.Keys <= (m'.Keys + os');
  // assert m.Keys !! os;

assert MapOK(m);

  print "CALL walkiesClean:", fmtobj(a), " owner:", fmtobj(o), " ", |os|, "\n";

assert AOK(b,oHeap);
assert forall o <- (oHeap) :: AOK(o,oHeap);
assert m'.Keys <= oHeap;  
assert forall o <- (m'.Keys) :: AOK(o,oHeap);
assert forall o <- (m.Values) :: AOK(o,oHeap + m'.Values);

label HEAP_OK:

  // assert b.Valid() && b.TRUMP();
  // assert forall o <- oHeap    :: o.TRUMP() && o.Valid();
  // assert forall o <- m.Values :: o.TRUMP() && o.Valid();
  // assert forall o <- (oHeap) :: (o.AllOutgoingReferencesAreOwnership(oHeap));
  // assert forall o <- (oHeap) :: (o.AllOutgoingReferencesWithinThisHeap(oHeap));
  // assert forall o <- (oHeap) :: (o.AllOwnersAreWithinThisHeap(oHeap));
  // assert forall o <- (m.Values) :: (o.AllOutgoingReferencesAreOwnership(oHeap + m.Values));
  // assert forall o <- (m.Values) :: (o.AllOutgoingReferencesWithinThisHeap(oHeap + m.Values));
  // assert forall o <- (m.Values) :: (o.AllOwnersAreWithinThisHeap(oHeap + m.Values));

  if (a in m') { 
        b := m'[a]; 
        print "RETN walkiesClean ", fmtobj(a)," already cloned,  returning ",fmtobj(b), "\n";
  
        assert AOK(b,oHeap + m'.Values);

        assert AllOK(oHeap, oHeap);
        assert AOK(b, oHeap + m.Values);
        assert AllOK(m.Values, oHeap + m.Values);
        assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
        assert (m.Keys + os) == (m'.Keys + os') == oHeap;
        assert m.Keys <= oHeap;  ///mmmKJX - Important point
        assert m.Keys !! os;
        assert mapLEQ(m',m);
        assert m[a] == b;  //mmmKJX
        assert (a in m.Keys) ==> (m[a] == b);  //mmmKJX

        assert a in m.Keys;   //mmmKJX
        assert b in m.Values; //mmmKJX
        assert (m[a] == b);   //mmmKJX
        assert os  == oHeap - m.Keys;
        assert MapOK(m);
        return;
        }

  assert a in oHeap;
  assert a !in m.Keys;
  assert os  == oHeap - m.Keys;  //FUCK FUCK
  assert a in os;


  assert AllOK(oHeap);
  assert AllOK(m.Keys, oHeap);
  assert AllOK(m.Values, oHeap+m.Values);

//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
  // if (a !in os') { 
  //     print "RETN walkiesClean currently processing ", fmtobj(a),"\n";

  //     assert AOK(b,oHeap);
  //     assert forall o <- (oHeap) :: AOK(o,oHeap);
  //     assert forall o <- (m'.Values) :: AOK(o,oHeap + m'.Values);

  //   assert o in oHeap;
  //   assert os <= oHeap;
  //   assert AllOK(m'.Values, oHeap + m'.Values);
  //   assert  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
  //   assert  m'.Keys !! os;
  //   assert  a !in os;

  // assert AllOK(oHeap, oHeap);
  // assert AOK(b, oHeap + m.Values);
  // assert AllOK(m.Values, oHeap + m.Values);
  // assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
  // assert m.Keys <= (m'.Keys + os');
  // assert m.Keys !! os;
  // assert mapLEQ(m',m);

  // assert (a in m.Keys) ==> (m[a] == b);  //mmmKJX

  // //mmmKJX  FUUUCK
  // arseume {:axiom} a in m.Keys;   //mmmKJX  FUUUCK
  // arseume {:axiom} b in m.Values; //mmmKJX  FUUUCK
  // arseume {:axiom} (m[a] == b);   //mmmKJX  FUUUCK
  // //mmmKJX  FUUUCK
  //     return;
  //      }
//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
  assert a in os';
  assert a in oHeap;
  assert AOK(a,oHeap);
  assert MapOK(m);
  assert ({a} + a.AMFO) <= oHeap;
  var delta := ({a} + a.AMFO) - m'.Keys;
  assert delta !! m'.Keys;
  assert delta <= oHeap; 

  assert AllOK(delta, oHeap);


  print "walkiesClean started on:", fmtobj(a), "\n";
  
  assert NOAM: a !in m'.Keys;
  assert forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
  assert MapOK(m);
  //assert os  == oHeap - m.Keys;  // so given we've just whippedw A o out of os  
                                   //this really really shojldnt hefucek work


// KJX (FWE're sharigh i.e. (not(inside(x,o)), so (a-==b) , 
// we don['t need to clone the fields, do we?]
// I don't think it's a problem if we do, though,
// on reflection, probably would be a proboem - fdepending.
// SO LETS NOT DO IT!

  if (not(inside(a,o))) {
        print "RETN walkiesClean ", fmtobj(a), " is outside ", fmtobj(o), "so maps to itself (share not clone)\n";

        assert MapOK(m);
        assert MapOK(m');

        assert m.Keys == m'.Keys;

        assert AllOK(oHeap);
        assert AllOK(m.Keys, oHeap); 
        assert AllOK(m'.Keys, oHeap); 
        
        
        assert MKPRIME: AllOK(m'.Keys, oHeap); 
        var mprime_keys := m'.Keys;

        assert AllOK(m.Values, oHeap+m.Values);
        assert AllOK(m'.Values, oHeap+m.Values);


        assert a !in m'.Keys;

        assert os  == oHeap - m.Keys; 


        ImOutsideSoAreAllMyOwners(a, o, oHeap);
        assert forall oo <- a.AMFO :: not(inside(oo,o));
        assert forall d <- delta :: not(inside(d,o));
        assert forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
        assert NODL: forall d <- delta :: (d in m') ==> (m'[d] == d);

        //we're sticking a->a into m - but should we even bother to do that?
        b := a;

        os := os' - {a};
        assert OSNOA: a !in os;
        assert a !in m'.Keys;
        assert a in delta;

        assert os == os' - {a};
        // // delta := delta * os'; 
        // assert delta <= os';

        assert delta <= oHeap; 
        assert AllOK(delta, oHeap);
        
        AllMyOwnersWillWitherAway(a, oHeap);
        assert forall oo <- a.AMFO :: AOK(oo, oHeap);

        assert delta == ({a} + a.AMFO) - m'.Keys;
        assert delta !! m'.Keys;

        a.AMFOsisAMFOs();
        assert forall oo <- a.AMFO :: oo.AMFO <= a.AMFO;
        assert forall oo <- {a} + a.AMFO :: oo.AMFO <= a.AMFO;
        assert forall oo <- delta :: oo.AMFO <= a.AMFO;



        os := os - delta;

        // assert delta !! os;

        // var idAMFOs := set2idMap(delta); 
        // assert idAMFOs.Keys == idAMFOs.Values == delta;
        // assert a  in idAMFOs.Keys;
        // assert idAMFOs[a] == a;
        // assert idAMFOs[a] == b;


        assert a !in m'.Keys by { reveal NOAM; }
        assert MapOK(m');



//         assert mprime_keys == m'.Keys;

//         assert old@MKPRIME(AllOK(m'.Keys, oHeap));
//         assert unchanged@MKPRIME(m'.Keys);
//         assert unchanged@MKPRIME(oHeap);
// // assert unchanged (set o1 <- oHeap, o2 <- o1.ValidReadSet() :: o2`fields);
// // assert unchanged (set o1 <- oHeap, o2 <- o1.ValidReadSet() :: o2`fieldModes);

//           assert forall x <- oHeap :: old( x.fields ) == x.fields;
//           assert forall x <- oHeap :: old( x.fieldModes ) == x.fieldModes;

          assert AllOK(oHeap) by { 
            reveal HOK; 
            assert old@HOK(AllOK(oHeap));
            assert unchanged(oHeap);
            AllOKtardis@HOK(oHeap, oHeap);
            assert AllOK(oHeap);
             }
          assert m'.Keys  <= oHeap ;
          assert AllOK(m'.Keys, oHeap) by {reveal KOK; assert AllOK(m'.Keys, oHeap);}


          // assert unchanged(oHeap`fields, oHeap`fieldModes );
          // assert forall x <- oHeap :: unchanged( x`fields );
          // assert forall x <- oHeap :: unchanged( x`fieldModes );


          // assert forall x <-  m'.Keys :: old( x.fields ) == x.fields;
          // assert forall x <-  m'.Keys :: old( x.fieldModes ) == x.fieldModes;

          // assert forall x <- m'.Keys :: old@MKPRIME(AOK(x,oHeap));
          // assert forall x <- oHeap :: (AOK(x,oHeap));

          // assert AllOK(m'.Keys, oHeap);

        // assert AllOK(m'.Keys, oHeap) by { 
        //   assert old@MKPRIME(AllOK(m'.Keys, oHeap));
        //   assert unchanged@MKPRIME(m'.Keys);
        //   assert unchanged@MKPRIME(oHeap);
        //   reveal MKPRIME;
        //     assert AllOK(m'.Keys, oHeap);
        //    }

  a.AMFOsisAMFOs();
  assert forall oo <- delta :: oo.AMFO <= a.AMFO;
  a.AMFOsisAMFOs2();
  assert forall x <- delta, oo <- x.AMFO :: oo.AMFO <= a.AMFO;

  assert deltaAMFOs: forall x <- delta, oo <- x.AMFO :: oo.AMFO <= a.AMFO;

  // assert forall oo <- idAMFOs.Keys :: oo.AMFO <= a.AMFO;
  // assert (forall x <- m'.Keys, oo <- x.AMFO :: oo in m'.Keys);

  //       m := idAMFOs + m'; ///NOTE that this is an assymmetric add - retains all of m', fills in from idAMFOs

  // assert idAMFOs.Keys   == delta;
  // assert idAMFOs.Values == delta;
  // assert idAMFOs == map x <- delta :: x := x;

  m := Extend_A_Map(m',delta);

  assert m'.Keys + delta == m.Keys;
  assert delta !! m'.Keys;
  //  arseume delta !! m'.Values;

  assert m'.Values + delta == m.Values;








  assert forall x <- m'.Keys :: m[x] == m'[x];

  assert forall x <- m.Keys | x in m'.Keys :: m[x] == m'[x];

  assert forall x <- m.Keys | x in m'.Keys :: x in m.Keys && m[x] == m'[x]; //redunant test for m!

  assert forall x <- m.Keys :: 
        if (x in m'.Keys) then (m[x] == m'[x]) else (x in delta && (m[x] == x));

  assert forall x <- m'.Keys, oo <- x.AMFO :: oo in m'.Keys && m'[oo] in m'[x].AMFO;

  assert forall x <- m.Keys, oo <- x.AMFO |
                            (x in m'.Keys) :: oo in m'.Keys && m'[oo] in m'[x].AMFO;



  assert GARFUNKLE: forall x <- m.Keys, oo <- x.AMFO |
                            (x in m'.Keys) :: oo in m'.Keys && m'[oo] in m'[x].AMFO;

// ////WE WANT THIS                  
//   assert forall x <- m.Keys, oo <- x.AMFO |
//                             (x in m'.Keys) :: oo in m.Keys && m[oo] in m[x].AMFO;
////

  forall x <- m.Keys, oo <- x.AMFO 
 //    ensures  (oo in m.Keys && m[oo] in m[x].AMFO)
     ensures  (m[oo] in m[x].AMFO)
     {
       if (x in m'.Keys) {       //could be great; coiuld not be...
          assert m[x] == m'[x];   ///note not necessarily "insire" = outside, already copiied

assert
            && m[x] == m'[x]
            && (oo in m'.Keys)
            && (oo in m.Keys) 
            && m'[oo] in m'[x].AMFO
            && m[oo] == m'[oo] 
            && m[oo] in m[x].AMFO
            ;

      assert oo in m'.Keys && m'[oo] in m'[x].AMFO;
      assert oo in m.Keys && m[oo] in m'[x].AMFO;
      assert oo in m'.Keys && m'[oo] in m[x].AMFO;
      assert oo in m.Keys && m[oo] in m[x].AMFO;

          // assert oo in m'.Keys && m'[oo] in m'[x].AMFO;
          // assert oo in m.Keys  && m[oo]  in  m[x].AMFO;
       } else {
           assert x in delta;  //must be outside
           assert x in m.Keys;
           assert x == m[x];
           assert x.AMFO == m[x].AMFO;
           assert oo in x.AMFO;
           assert oo in m[x].AMFO;
           assert m[oo] == oo;
           assert m[oo] in m[x].AMFO;
       }
       assert (oo in m.Keys && m[oo] in m[x].AMFO);



     }

//IF we can't assert it
//can we assyume it all and carry on?
//assert forall x <- m.Keys, oo <- x.AMFO :: (oo in m.Keys && m[oo] in m[x].AMFO);

assume forall x <- m.Keys, oo <- x.AMFO :: (oo in m.Keys && m[oo] in m[x].AMFO); //proved ibn forall/ensuring
assume forall x <- m.Keys, oo <- x.AMFO :: (m[oo] in m[x].AMFO); 

assert FUKA: forall x <- m.Keys, oo <- x.AMFO :: (m[oo] in m[x].AMFO) //proved ibn forall/ensuring
 by { assume forall x <- m.Keys, oo <- x.AMFO :: (m[oo] in m[x].AMFO); 
      assert forall x <- m.Keys, oo <- x.AMFO :: (m[oo] in m[x].AMFO); 
  }

  // assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys  && m[oo] in m[x].AMFO 
  //   by { 

  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) != (x in delta);
  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==> m[x] == m'[x];
  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==> oo in m'.Keys && m'[oo] in m'[x].AMFO;
  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==> m[x] == m'[x] && (oo in m'.Keys) && (oo in m.Keys);

  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==> 
  //           && m[x] == m'[x]
  //           && m[x].AMFO == m'[x].AMFO
  //           ;

  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==>            
  //           && (oo in m'.Keys)
  //           && (oo in m.Keys) 
  //           && m[oo] == m'[oo]
  //           ;


  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==>            
  //           oo in m'.Keys && m'[oo] in m'[x].AMFO;

  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==>            
  //          oo in m.Keys && m[oo]  in m'[x].AMFO;

  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==>            
  //           oo in m'.Keys && m'[oo] in m[x].AMFO;

  //       assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==>            
  //         oo in m.Keys  && m[oo]  in m[x].AMFO
  //          ;


        // assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==> 
        //   (oo in m.Keys  && m[oo] in m[x].AMFO);

        // assert forall x <- m.Keys, oo <- x.AMFO :: (x !in m'.Keys) ==> (
        //    && x in m.Keys
        //    && x == m[x]
        //    && x.AMFO == m[x].AMFO
        //    && oo in x.AMFO
        //    && oo in m[x].AMFO
        //    && m[oo] == oo
        //    && m[oo] in m[x].AMFO
        // );
        // assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==> m[x] == m'[x];
        // assert forall x <- m.Keys, oo <- x.AMFO :: (x in m'.Keys) ==> (oo in m.Keys && m[oo] in m[x].AMFO);

        // assert forall x <- m.Keys, oo <- x.AMFO :: (x !in m'.Keys) ==> m[x] == x;
        // assert forall x <- m.Keys, oo <- x.AMFO :: (x !in m'.Keys) ==> (oo in m.Keys && m[oo] in m[x].AMFO);

        // assert forall x <- m.Keys, oo <- x.AMFO :: (oo in m.Keys && m[oo] in m[x].AMFO);
    //  }

//   assert forall x <- m.Keys :: 
//         if (x in m'.Keys) then
//             (forall oo <- x.AMFO ::  oo in m'.Keys && m'[oo] in m'[x].AMFO)
//         else (x in delta && (m[x].AMFO == x.AMFO) &&         
//             (forall oo <- x.AMFO ::  oo in m.Keys && m[oo] in m[x].AMFO));

  // assert forall x <- m.Keys, oo <- x.AMFO ::
  //   if (oo in m'.Keys) then (m[oo] in m[x].AMFO)
  //     else ((oo in delta) && (m[oo] == oo) && (oo in m[x].AMFO));




assert m.Keys <= oHeap;

  forall x <- m.Keys ensures  ( AOK(x, oHeap) ) {
    if (x in m'.Keys)
         {
          reveal KOK;
          assert old@KOK(AllOK(m'.Keys, oHeap));
          assert old@KOK(AOK(x, oHeap));
          AOKtardis@KOK(x, oHeap);
          assert AOK(x, oHeap);
         }
        else {assert (x in delta) &&  (AOK(x,oHeap));}}


//MapOK() expanded
  
  assert (forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys);
  assert (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?);
  forall x <- m.Keys |  x.region.Heap? ensures (x.region.owner in x.AMFO) 
   {
     assert m.Keys <= oHeap;
     assert x in oHeap;
     assert AOK(x,oHeap);
     assert x.Valid();
     assert x.OwnersValid();
     assert x.region.owner in x.AMFO;
   }
    
  assert (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys);

   assert (forall x <- m'.Keys, oo <- x.AMFO :: oo in m'.Keys && m'[oo] in m'[x].AMFO) 
    by {
      reveal KAMFOK;
      //assert old@KAMFOK(forall x <- m'.Keys, oo <- x.AMFO :: m'[oo] in m'[x].AMFO);
      assert           (forall x <- m'.Keys, oo <- x.AMFO :: m'[oo] in m'[x].AMFO);
    }



  assert forall x <- m'.Keys, oo <- x.AMFO :: oo in m'.Keys && m'[oo] in m'[x].AMFO
    by { reveal KAMFOK; }
    

  assert forall x <- m'.Keys :: 
     if (inside(x,o))
       then ((m'[x] !in oHeap) && (UniqueMapEntry(m',x))) 
       else (m'[x] == x);


  assert AllOK(m'.Keys, oHeap);
  assert AllOK(m'.Values, oHeap+m'.Values);

  // forall x <- m.Keys ensures (
  //    if (inside(x,o))
  //      then ((m[x] !in oHeap) && (UniqueMapEntry(m,x))) 
  //      else (m[x] == x)
  // ) {
  //   if (x in m'.Keys) { assert AOK(x, oHeap); assert AOK(m[x], oHeap+m'.Values);}
  //     else {  assert x in delta;  assert x in oHeap; assert x == m[x];  assert AOK(m[x], oHeap+m'.Values); 
  //     }}



  //  assert (forall x <- m'.Keys, oo <- x.AMFO :: oo in m'.Keys && m'[oo] in m'[x].AMFO);
  //  assert delta == ({a} + a.AMFO) - m'.Keys;
  //  assert m.Keys == m'.Keys + delta;
  //  assert (forall x <- m.Keys - m'.Keys :: x in delta);

   //assert (forall x <- m.Keys - m'.Keys :: (x in delta) && (x in m.Keys));
   //assert (forall x <- m.Keys - m'.Keys, oo <- x.AMFO :: (oo in delta) && (oo in m.Keys));

  // assert forall x <- m'.Keys, oo <- x.AMFO :: oo in m'.Keys && m'[oo] in m'[x].AMFO;

  // assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys  && m[oo] in m[x].AMFO;



  //  forall x <- delta,   oo <- x.AMFO ensures oo in delta && m'[oo] in m'[x].AMFO 
  //  {
  //    reveal deltaAMFOs;

  //    assert forall oo <- x.AMFO :: oo.AMFO <= a.AMFO; 
  //  }

  //  assert (forall x <- 'm.Keys - m'.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);

  //  forall x <- m.Keys, oo <- x.AMFO ensures ((oo in m.Keys) && (m[oo] in m[x].AMFO)) {
  //   if (x in m'.Keys) { assert FUCKER1: (oo in m.Keys) && (m[oo] in m[x].AMFO); }
  //       else {
  //         assert x in delta; assert FUCKER2: m[oo] in m[x].AMFO;
  //       } }



   forall x <- m.Keys |  x.region.Heap? ensures (m[x.region.owner] == m[x].region.owner)
     {
       assert x.region.owner in x.AMFO;
       if (x in m'.Keys) {
        assert MapOK(m');
        assert (m'[x.region.owner] == m'[x].region.owner);
        assert (m[x.region.owner] == m[x].region.owner);
       } else {
        assert x in delta;
        // assert x in idAMFOs.Keys;
        // assert idAMFOs[x] == x;
        x.AMFOsisAMFOs();
        assert m[x.region.owner] == m[x].region.owner;
        // assert (idAMFOs[x.region.owner] == idAMFOs[x].region.owner);
       }
     }
 
 

assert AllOK(m.Values, oHeap+m.Values) by { 
  
  reveal VOK; reveal MAPOK0; 

   forall x : Object <- m.Keys ensures (AOK(m[x], oHeap+m.Values))
    {
       assert x in oHeap;
       assert AllOK(oHeap);
       if (x in m'.Keys) {
        assert MapOK(m');
        assert old@VOK(AllOK(m'.Values, oHeap+m'.Values));
        AllOKtardis@VOK(m'.Values, oHeap+m'.Values);
        assert        (AllOK(m'.Values, oHeap+m'.Values));
        assert AOK(m'[x], oHeap+m'.Values);
        assert m'[x] == m[x];
        assert AOK(m[x], oHeap+m'.Values);
        assert mapLEQ(m',m);
        AOKWiderContext(m[x],  oHeap+m'.Values, (oHeap+m.Values) -  (oHeap+m'.Values));

         assert AOK(m[x], oHeap+m.Values);
       } else {
        assert x in delta;
        // assert x in idAMFOs.Keys;

        // assert idAMFOs[x] == x;

        assert m[x] == x;
        assert x in oHeap;
        assert AllOK(oHeap);
        assert AOK(m[x], oHeap);
        AOKWiderContext(m[x], oHeap, m.Values);
        assert AOK(m[x], oHeap+m.Values);

       }
     }
     assert AllOK(m.Values, oHeap+m.Values);
}

/////////////////////////////  /////////////////////////////  /////////////////////////////
// unpacking MapOK(m)
/////////////////////////////  /////////////////////////////  /////////////////////////////

  
  forall x <- m.Keys, oo <- x.AMFO ensures oo in m.Keys
    {
      x.AMFOsisAMFOs();
    }
  assert (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?);
  assert (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO);
  assert (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys);
  assert (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner );
  assert (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO);
  assert forall oo <- (a.AMFO - {a}) :: oo in m.Keys;
  assert forall oo <- (a.AMFO - {a}) :: m[oo] in b.AMFO;
  assert m[a] == b;
/////////////////////////////  /////////////////////////////  /////////////////////////////
/////////////////////////////  /////////////////////////////  /////////////////////////////
  assert MapOK(m);
/////////////////////////////  /////////////////////////////  /////////////////////////////
/////////////////////////////  /////////////////////////////  /////////////////////////////








        assert unchanged(oHeap);
        assert AllOK(oHeap) by { reveal HOK; }
        assert AllOK(m.Keys, oHeap);
        assert AllOK(m.Values, oHeap+m.Values) by { reveal VOK; reveal MAPOK0; }
        assert MapOK(m);  //DEEZ FUCKED

        assert forall k <- m.Keys :: (k in m'.Keys) || ((k in os') && k !in os);
        assert a in m.Keys;
        // assert idAMFOs[a] == a == b;
        assert       m[a] == a == b;
        // MappingPlusKeysValues(idAMFOs,m',m);
        assert mapLEQ(m', m);

        assert os' == oHeap - m'.Keys;
        assert os  == os'- delta;
        assert m.Keys == m'.Keys + delta;
        assert os'- delta == oHeap - (m'.Keys + delta);
        
        assert os  == oHeap - m.Keys;
        
        // assert idAMFOs[a] == a == b;
        assert       m[a] == a == b;

        assert forall d <- delta :: d in m.Keys ==> m[d] == d;
 
        assert b in m.Values;
        assert delta <= m.Values;
         

        assert AllOK(m'.Values, oHeap + m'.Values) by {
          reveal VOK;
          assert old( AllOK(m'.Values, oHeap + m'.Values) );
          AllOKtardis(m'.Values, oHeap + m'.Values);
          assert ( AllOK(m'.Values, oHeap + m'.Values) ); 
       //   assert ( AllOK(m.Values, oHeap + m.Values) );       // DEEZ BROKEN                       
                                                          }

// m := m';  //WTIF IS THIS JUST A MISTAKE
// (gone bno)


   assert AllOK(m.Values, oHeap + m.Values);     // DEEZ BROKEN         


  
  assert AllOK(oHeap, oHeap) by { 
    reveal HOK;
    assert unchanged@HOK(oHeap);
    AllOKtardis@HOK(oHeap, oHeap);
    assert AllOK(oHeap, oHeap);
         }
  assert AOK(b, oHeap + m.Values);
  assert AllOK(m.Values, oHeap + m.Values);

  assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
  assert m.Keys <= (m'.Keys + os');
  assert m.Keys !! os;
  assert mapLEQ(m',m);
  assert (a in m.Keys) ==> (m[a] == b);  //mmmKJX
  assert (m[a] == b);  //mmmKJX

  assert a in m.Keys;   //mmmKJX
  assert b in m.Values; //mmmKJX
  assert (m[a] == b);   //mmmKJX

  assert MapOK(m); 
        return;  
  }//end if not inside

assert inside(a,o);
assert forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));

//         assert mapLEQ(m', m);
//         AllOKWiderContext(m'.Values, oHeap + m'.Values, delta);
//         assert AllOK(m'.Values, oHeap + m'.Values + delta);
 

  // assert (a in os') && (a !in os);  ///so we are working on "a" now!
  // assert a !in m'.Keys;  ///but not yet done

  var bInMValues := false;
  assert BIMV: bInMValues ==> b in m.Values;

  assert AllOK(oHeap);

  assert HOIKS: AllOK(oHeap);

  assert MapOK(m);

  if (a.region.Heap?) {
        print "walkiesClean owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";

//PRECONDITIONS
        assert MapOK(m);

        assert AllOK(oHeap, oHeap) by {  
            reveal HOK;
            assert old( AllOK(oHeap, oHeap) );
            AllOKtardis(oHeap, oHeap);
            assert AllOK(oHeap, oHeap);
            }
        assert a.region.owner in oHeap by {
          reveal HOK, AOK;
          assert a in oHeap;
          AOKAMFO(a,oHeap);
          assert a.region.owner in a.AMFO;
          assert AOK(a.region.owner,oHeap);
          assert a.region.owner in oHeap;
            }
        assert o in oHeap;
        assert os <= oHeap;
        assert AllOK(m'.Values, oHeap + m'.Values);
        assert  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
    //    assert  m'.Keys !! os;
    //    assert  a !in os;
    //    assert  a !in (oHeap - m'.Keys);
        assert MapOK(m);
        assert mapLEQ(m',m);
        assert os == oHeap - m'.Keys;

        var rowner, rm,ros := walkiesClean(a.region.owner, o, m', os, oHeap);

        assert MapOK(rm);
        assert ros == oHeap - rm.Keys;
        assert AOK(rowner, oHeap + rm.Values);
        assert AllOK(oHeap, oHeap);
        assert AllOK(rm.Values, oHeap + rm.Values);
        assert RMOK: AllOK(rm.Values, oHeap + rm.Values);
        assert forall x <- rm.Keys :: (not(inside(x,o)) ==> (rm[x] == x));
        assert ros <= os;
        // assert a !in ros by { 
        //           assert a !in os;
        //           assert ros <= os; 
        //           assert a !in ros;
        //           }

        assert rm.Keys <= (m'.Keys + os');
        assert rm.Keys !! ros;
        assert mapLEQ(m',rm); 
        assert MapOK(rm);
        assert MapOKHere: MapOK(rm);
        assert AllOK(rm.Values, oHeap + rm.Values);

        ///BUT things hop around insidef, e.g. so we've already copied "a" in the recursive call
        ///can we just be done?
        ///Hmm. fuck I hate this shit

        if (a in rm.Keys) {
            m := rm;
            os := ros;
            b := rm[a];
            return; //should work because walkiesClean meets all the conditiosn, right???
        }

  assert a !in rm.Keys;
  assert ros == oHeap - rm.Keys;

  assert AllOK(oHeap, oHeap);
  assert AllOK(rm.Values, oHeap + rm.Values) by { reveal RMOK;}
  AllOKWiderContext(oHeap, oHeap, rm.Values);
  AllOKWiderFocus(oHeap, rm.Values, oHeap + rm.Values);
  assert AllOK(oHeap + rm.Values, oHeap + rm.Values);
  label JBF:
        b := new Object.make(protoTypes, rowner, oHeap+rm.Values, "clone of " + a.nick);
  assert old@JBF(AllOK(oHeap + rm.Values, oHeap + rm.Values));
  assert unchanged@JBF(  oHeap + rm.Values );
  assert unchanged@RMOK( oHeap + rm.Values );

  AllOKtardis@JBF(oHeap + rm.Values, oHeap + rm.Values);

  assert AllOK(oHeap + rm.Values, oHeap + rm.Values);
  AllOKtardisSubset@JBF(oHeap,  oHeap + rm.Values, oHeap,  oHeap + rm.Values);
  assert AllOK(oHeap, oHeap);

        assert fresh(b);
        assert b !in oHeap;
        assert b !in rm.Values;
        assert a !in rm.Keys;
        assert BOK: AOK(b, {b} + oHeap+rm.Values);
   assert a.region.Heap? == b.region.Heap?;



        assert forall x <- rm.Keys :: (not(inside(x,o)) ==> (rm[x] == x));
        assert ros  == oHeap - rm.Keys;

        assert a !in rm.Keys;
        assert b !in rm.Keys;
   assert rm.Keys <= oHeap;

///precondtion for HURRAY_DAFNY

  assert MapOK(rm) by {reveal MapOKHere;}
   assert a.region.Heap? == b.region.Heap?;

  assert (forall x <- rm.Keys, oo <- x.AMFO :: oo in rm.Keys);
  assert (forall x <- rm.Keys :: x.region.Heap? == rm[x].region.Heap?);
  assert (forall x <- rm.Keys |  x.region.Heap? :: x.region.owner in x.AMFO);
  assert (forall x <- rm.Keys |  x.region.Heap? :: x.region.owner in rm.Keys);
  assert (forall x <- rm.Keys |  x.region.Heap? :: rm[x.region.owner] == rm[x].region.owner );
  forall x <- rm.Keys, oo <- x.AMFO ensures (rm[oo] in rm[x].AMFO)
    {
      assert oo in rm.Keys;
      assert MapOK(rm);
      assert (rm[oo] in rm[x].AMFO);
    }

  assert MapOK(rm);
  assert AllOK(oHeap);
  assert a in oHeap;  
   assert AOK(a, oHeap);
   assert a.Valid();
   assert a.region.Heap? ==> a.region.owner in a.AMFO;
   assert a.region.Heap? ==> a.region.owner in rm.Keys;


assert forall x <- rm.Keys, oo <- x.AMFO :: (rm[oo] in rm[x].AMFO);
assert (a.AMFO - {a}) <= rm.Keys;
assert forall oo <- (a.AMFO - {a}) :: (rm[oo] in b.AMFO);

   assert  a.region.Heap? ==> rm[a.region.owner] == b.region.owner;



   assert AllOK(oHeap);
   assert AllOK(rm.Values, oHeap + rm.Values);
   assert AOK(b, oHeap + rm.Values + {b});

   //maintaing MapOK


        //m := rm[a:=b];
        m := HURRAY_DAFNY(rm, a, b, oHeap);
        
        assert a in m.Keys;
        assert m[a] == b;
        assert m == rm[a:=b];
        assert m.Keys == rm.Keys + {a};
        assert a !in oHeap - m.Keys;

        os := ros - {a};
//        assert os  == oHeap - m.Keys;

        forall x <- m.Keys ensures (not(inside(x,o)) ==> (m[x] == x))  {
            if (x in rm.Keys) {assert not(inside(x,o)) ==> (m[x] == x);}
              else {
                        assert inside(a,o);
                       assert inside(x,o);
              } }


        assert m == MappingPlusOneKeyValue(rm,a,b);

        assert a !in rm.Keys;
        assert a in m.Keys && m[a] == b;
        assert m.Keys == rm.Keys + {a};

        assert b !in (oHeap+rm.Values); 
        assert b !in (oHeap);
        assert b !in (rm.Values); //yes, but SHOULD IT BE - why not?
        assert b in m.Values;
        assert m.Values == rm.Values + {b};
        assert RMB: m.Values == rm.Values + {b};

        assert b in m.Values;
        bInMValues := (b in m.Values);
        assert BIMV2: bInMValues ==> b in m.Values;

        assert forall k <- m.Keys   :: ((k  in rm.Keys) ==> (m[k] == rm[k])); 
        assert forall k <- m.Keys   :: ((k !in rm.Keys) ==> ((k == a) && (m[k] == b)));

//these ensure the mapping is injective.   but do we really care?
//or rather: Do we need to care?
      //  assert forall k <- m.Keys   :: (k in rm.Keys  ) != (k == a);
      //  assert forall v <- m.Values :: (v in rm.Values) != (v == b);


       assert m == rm[a:=b];
       assert MapOK(m);

        assert AllOK(rm.Values, oHeap + rm.Values) by {
              // reveal RMOK;
              assert unchanged@JBF( oHeap + rm.Values );
   AllOKtardisSubset@JBF(rm.Values,  oHeap + rm.Values, rm.Values,  oHeap + rm.Values);
            assert AllOK(rm.Values, oHeap + rm.Values); 
             }
        assert AOK(b, {b} + oHeap+rm.Values);
        assert m.Values == rm.Values + {b} by { reveal RMB; }
//        assert m.Values - rm.Values == {b} by { reveal RMB; }
 //       assert (oHeap+m.Values) == (oHeap+rm.Values) + {b};

        AllOKWiderContext(rm.Values, (oHeap+rm.Values), {b});
        assert AllOK(rm.Values, (oHeap+rm.Values)+{b});
        assert (oHeap+rm.Values)+{b} == (oHeap+m.Values);
        assert AllOK(rm.Values, (oHeap+m.Values));

        assert AOK(b, {b} + oHeap+rm.Values);
        assert AOK(b, (oHeap+m.Values));

        AllOKWiderFocus(rm.Values, {b}, (oHeap+m.Values));
        assert AllOK(rm.Values + {b}, (oHeap+m.Values));
        assert AllOK(m.Values, (oHeap+m.Values));

        assert MMOK: AllOK(m.Values, (oHeap+m.Values));
        


        assert AllOK(oHeap, oHeap) by {  
          reveal HOK;
          assert old( AllOK(oHeap, oHeap) );
          AllOKtardis(oHeap, oHeap);
        }

        assert AOK(b, oHeap+m.Values) by
        {
          assert AOK(b, {b} +oHeap+rm.Values) by { reveal BOK; }
          assert mapLEQ(rm, m); 
          MapLEQKeysValues(rm, m);
          assert b in m.Values;
          assert ({b} +oHeap+rm.Values) <= oHeap+m.Values;
          assert AOK(b, oHeap+m.Values);
        }

        assert AllOK(m.Values, oHeap + m.Values) by {  
            reveal MMOK;
            assert old@MMOK( AllOK(m.Values, (oHeap+m.Values)) );
            AllOKtardis@MMOK(m.Values, (oHeap+m.Values));

            assert AllOK(m.Values, (oHeap+m.Values));
        }

       //// os := ros;  //dunno where best to do this.. tis dones't weem to be it...

        assert AllOK(oHeap, oHeap);
        assert AOK(b, oHeap + m.Values);
        assert AllOK(m.Values, oHeap + m.Values);
        assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
        assert m.Keys <= (m'.Keys + os');
        assert m.Keys !! os;

        assert mapLEQ(m',m);
        assert os  == oHeap - m.Keys;
        assert MapOK(m);
        assert AllOK(oHeap, oHeap);

      //EBD HEAP OBJECT
    } else {
      //"world"" OBJECT
        assert AllOK(oHeap, oHeap);   

        print "walkiesClean world:", fmtobj(a),"\n";

        label ERE:
          assert AllOK(oHeap, oHeap);

        b := new Object.frozen2(protoTypes, oHeap);

        assert unchanged@ERE( oHeap );

        assert AllOK(oHeap, oHeap);
        assert AOK(b,{b});

        b.nick := "clone of" + a.nick;
        m := m'[a:=b];
        assert m == MappingPlusOneKeyValue(m',a,b);
        assert m[a] == b;

        os := os - {a};
        assert os  == oHeap - m.Keys;

        assert b in m.Values;
        assert      m.Values == m'.Values + {b};
        assert MVB: m.Values == m'.Values + {b};

        AOKWiderContext(b,{b}, oHeap + m.Values);
        assert b in m.Values;
        assert ({b}  +oHeap+m.Values) <= oHeap+m.Values;
        assert AOK(b, oHeap+m.Values);

        assert b in m.Values;
        bInMValues := (b in m.Values);
        assert BIMV3: bInMValues ==> b in m.Values;


        assert AllOK(oHeap, oHeap); 
        assert AllOK(m.Values, oHeap + m.Values);
        assert MapOK(m);
           assert a.region.Heap? == b.region.Heap?;

        //end world object
  }

   assert a.region.Heap? == b.region.Heap?;
   assert b in m.Values;


    assert AllOK(m.Values, oHeap + m.Values);

  // assert AllOK(m.Values, oHeap + m.Values) by {
  //   reveal VOK;
  //   assert old@VOK(   AllOK(m'.Values, oHeap + m'.Values)   );
  //   AllOKtardis@VOK( m'.Values, oHeap + m'.Values);
  //   assert m.Values == m'.Values + {b} by {
  //             reveal BIMV;
  //             assert bInMValues == true;
  //             assert b in m.Values;
  //             }
  //   AllOKWiderContext( m'.Values, oHeap + m'.Values, {b} );
  //   AllOKtardis@VOK( m'.Values, oHeap + m'.Values);
  //   assert AOK(b,{b});
  //   AOKWiderContext(b,  {b}, oHeap + m.Values);
  //   assert b in m.Values;
  //   assert AOK(b, oHeap + m.Values);
  //   AllOKWiderFocus(m'.Values, {b}, oHeap + m.Values);
  //   assert AllOK(m.Values, oHeap + m.Values);
  // } 
  //  KJX FROM HERE END

  // assert AllOK(oHeap, oHeap);
  // assert AOK(b, oHeap + m.Values);
  // assert AllOK(m.Values, oHeap + m.Values);
  // assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
  // assert m.Keys <= (m'.Keys + os');
  // assert m.Keys !! os;
  // assert mapLEQ(m',m);

// aresume os <= os' - {a};
// aresume AllOK(oHeap, oHeap);
// aresume AOK(b, oHeap + m.Values);
// aresume AllOK(m.Values,oHeap + m.Values);
// aresume forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
// aresume m.Keys <= (m'.Keys + os');
// aresume m.Keys !! os;
// aresume mapLEQ(m',m);

assert MapOK(m);
assert AllOK(oHeap);

return;//////  CHOP OFF HALFWAUY

  assert os  == oHeap - m.Keys;



print "<<<<<<<<<<<\n";
print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";

  assert m[a] == b;  //mmmKJX
  // assert (a in m.Keys) ==> (m[a] == b);  //mmmKJX

assert b.Valid() && b.TRUMP();

print "<<<<<<<<<<<\n";
printmapping(m);
print "<<<<<<<<<<<\n";

  var ns : seq<string> := set2seq(a.fields.Keys);
  print "walkiesClean fields:", fmtobj(a), " fields=", fmtseqstr(ns), "\n";  

  assert os <= os' - {a};  //in case we also processed a bunch of idAMFOs





  assert AllOK(oHeap, oHeap);
  assert AOK(b, oHeap + m.Values);
  assert AllOK(m.Values, oHeap + m.Values);
  assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
  assert m.Keys <= (m'.Keys + os');
  assert m.Keys !! os;
  assert mapLEQ(m',m);



  for i := 0 to |ns|
     invariant os <= os' - {a}
     invariant b.Valid() && b.TRUMP()
     invariant mapLEQ(m',m)
     invariant a in oHeap
     invariant o in oHeap
     invariant os' <= oHeap
     invariant AllOK(oHeap, oHeap)
     invariant AllOK(m'.Values, oHeap + m'.Values)
     invariant  forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x))
     invariant  m'.Keys !! os' 
   {
        var n : string := ns[i];
        var ofv : Object := a.fields[n];   
    print "  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
    print "    (recurse on field ",n,")\n";

    // arseume a in oHeap;
    // arseume o in oHeap;
    // arseume os' <= oHeap;
    // arseume AllOK(oHeap, oHeap);
    // arseume AllOK(m'.Values, oHeap + m'.Values);
    // arseume forall x <- m'.Keys :: (not(inside(x,o)) ==> (m'[x] == x));
    // arseume m'.Keys !! os' ;

    // arseume os <= os' - {a};





        var rfv, rm, ros := walkiesClean(ofv, o, m, os, oHeap);

        assert rfv in rm.Values;
        // arseume rfv.AMFO <= rm.Values;

        assert m[a.fields[n]] == rfv;
        assert a.fields[n] !in ros;

        assert forall oo <- ofv.AMFO :: rm[ofv] in rfv.AMFO;

        if (rfv.region.Heap?) 
        {
          assert AOK(a,oHeap);
          assert a.AllOutgoingReferencesAreOwnership(oHeap);
          assert refOK(a,ofv);
          assert inside(a,ofv.region.owner);
          assert || ofv == a
                 || a in ofv.region.owner.AMFO;

//HERE
          assert inside(a,ofv.region.owner);

          assert inside(b, rfv.region.owner);
          assert refOK(b, rfv);
        } else {
          assert rfv.region.World?;
          assert refOK(b, rfv);
        }

        assert refOK(b, rfv);

        label HERE:

        b.fields := b.fields[n := rfv]; //  MOVED

        assert unchanged@HERE( oHeap - {b} );
        assert AllOK(oHeap - {b}, oHeap );

        assert refOK(b, rfv);

        os := ros;
        m  := rm;


  assert os  == oHeap - m.Keys;

        assert b.Valid() && b.TRUMP();

  assert AllOK(oHeap, oHeap);
  assert AOK(b, oHeap + m.Values);
  assert AllOK(m.Values, oHeap + m.Values);
  assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
  assert m.Keys <= (m'.Keys + os');
  assert m.Keys !! os;
  assert mapLEQ(m',m);
  assert m[a] == b;  //mmmKJX
  assert (a in m.Keys) ==> (m[a] == b);  //mmmKJX

   }
     print "RETN walkiesClean done ", fmtobj(a), " ", |os|, "\n";


    assert b.Valid() && b.TRUMP();

  assert AllOK(oHeap, oHeap);
  assert AOK(b, oHeap + m.Values);
  assert AllOK(m.Values, oHeap + m.Values);
  assert forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
//  assert m.Keys <= (m'.Keys + os');
  assert m.Keys !! os;
  assert mapLEQ(m',m);

  assert m[a] == b;  //mmmKJX
  assert (a in m.Keys) ==> (m[a] == b);  //mmmKJX

// arseume AllOK(oHeap, oHeap);
// arseume AOK(b, oHeap + m.Values);
// arseume AllOK(m.Values,oHeap + m.Values);
// arseume forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x));
// arseume m.Keys <= (m'.Keys + os');
// arseume m.Keys !! os;
  assert m[a] == b;  //mmmKJX
  assert (a in m.Keys) ==> (m[a] == b);  //mmmKJX

    assert a in m.Keys;   //mmmKJX
  assert b in m.Values; //mmmKJX
  assert (m[a] == b);   //mmmKJX

    assert os  == oHeap - m.Keys;
assert MapOK(m);

return;
}//end walkiesClean



lemma {:onlyAAKE} InTheFuckingMapValues<K,V>(k : K, v : V, m : map<K,V>)
  requires k in m.Keys
  requires v == m[k]
  ensures  v in m.Values
{}

lemma {:onlyAAKE} AlreadyInTheFuckingSet<E>(e : E, es : set<E>) 
        requires e in es
        ensures  ({e} + es) == es
        {}

// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



























method {:onlyfans} walkiesIsoOK(a : Object, b : Object, o : Object, m : Mapping, os' : set<Object>)
      returns (rv : bool, os : set<Object>)
  decreases os'
  ensures os <= os'
{
  rv := true;
  os := os';  assert os == os';

  print "CALL walkiesIsoOK:", fmtobj(a), " vs ", fmtobj(b), " owner:", fmtobj(o), " ", |os|, "\n";

//:todo - not caring about whether B is on os or not!
  if (a !in os) { 
        print "RETN walkiesIsoOK already processing ", fmtobj(a),"\n";
        assert os == os';
        return; }

  if (a == b) {
       print "RETN walkiesIsOK a == b ", fmtobj(a),"\n";
   
      if (inside(a,o)) {
          print "RETN walkiesIsoOK broken cos a==b at ", fmtobj(a), "but is inside clowner: ", fmtobj(o),"\n";
      rv := false;
      }
      
      return;
  }

  assert YEA: a  in os';

  print "walkiesIsoOK started on:", fmtobj(a), " vs ", fmtobj(b), "\n";
  os := os - {a};
  
  assert NOA: a !in os;
  
      if ((a !in m) || (m[a] != b))
    {
      print "RETN walkiesIsoOK broken:", fmtobj(a), " doesn't map to (or not in map) ", fmtobj(b),"\n";
      rv := false;
      return;
     }    

//print :todo go from region.owner to owner.region???

  if (a.region.Heap?) {
     print "walkiesIsoOK owners:", fmtobj(a), " vs ", fmtobj(b), " owned by ", fmtobj(a.region.owner) ,"\n";
     
    if (not(b.region.Heap?)) {
      print "RETN walkiesIsoOK broken:", fmtobj(a), " ", fmtobj(b), " cos ", a.region, " != ", b.region,"\n";
      rv := false;
      return;
     }     

     var rrv, ros := walkiesIsoOK(a.region.owner, b.region.owner, o, m, os);
     assert ros <= os;
     os := ros; rv := rrv; 
     assert os < os';

    if (!rrv) {
      print "RETN walkiesIsoOK broken:", fmtobj(a)," ", fmtobj(b), "owners did not compute\n" ;
      rv := false;
      return;
     }


  } else {
    print "walkiesIsoOK world:", fmtobj(a),"\n";
    if (b.region.Heap?) {
      print "RETN walkiesIsoOK broken:", fmtobj(a), " cos ", a.region, " != ", b.region,"\n";
      rv := false;
      return;
     }
  }
  
  assert SML: os < os';

  var ns : seq<string> := set2seq(a.fields.Keys);
  print "walkiesIsoOK fields:", fmtobj(a), " vs ", fmtobj(b), " fields=", fmtseqstr(ns), "\n";

    if (a.fields.Keys != b.fields.Keys) 
    {
      print "RETN walkiesIsoOK broken:", fmtobj(a), " fields «", a.fields.Keys, "» != ", fmtobj(b), " fields «", b.fields.Keys,"»\n";
      rv := false;
      return;
     }     


   assert os < os';

  for i := 0 to |ns| 
    invariant os < os'
   {
    var n : string := ns[i];
    var t : Object := a.fields[n];
    var u : Object := b.fields[n];
    print "  ",fmtobj(a),".",n," :=", fmtobj(t), "\n";
    print "  ",fmtobj(b),".",n," :=", fmtobj(u), "\n";
    print "    (recurse on field ",n,")\n";
    // assert a  in os' by { //////reveal YEA; }
    // assert a !in os  by { //////reveal NOA; }
    assert os < os';//  by { //////reveal SML; }
    var rrv, ros := walkiesIsoOK(t, u, o, m, os);
    assert ros <= os < os';
    os := ros;
    rv := rrv && rv; //or could just give up eagerly?
    assert os < os';
   }


  print "RETN walkiesIsoOK done ", fmtobj(a), " rv=", rv, " ", |os|, "\n";

    assert os < os'; //by { //////reveal SM2; }
}




























method {:onlyfans} checkIsoMapping(a : Object, o : Object, m : Mapping, os : set<Object>) returns (rv : bool)
  decreases os
{
 rv := false;
 print "cIM: CALL a:",fmtobj(a)," o:",fmtobj(o),"\n";

 if (a !in m)   { print "cIM: RETN a !in m   ", fmtobj(a), "\n"; return false; }

 if (a == m[a]) { print "cIM: RETN a == m[a] ", fmtobj(a), "\n"; return true;  }
   //hmm should *always* recurse if o in os
   //should NEVER reverse if o NOT in os?? yeah...
   //remember we are checking m NOT updqating it
  

 var b := m[a];

if (a !in os)   { print "cIM: RETN a !in os  ", fmtobj(a), "\n"; return true; }
   //TRUE because 

if (b !in os)   { print "cIM: RETN b !in os  ", fmtobj(b), "\n"; return false; }

if (a.region.Heap? && b.region.Heap?) {
  print "cIM: Heap? ",fmtobj(a), " and ", fmtobj(b), "    \n";
  print "    (doing recursive call on owners)";

  var ro := checkIsoMapping(a.region.owner, b.region.owner, m, os - {a});
  print "    (done recursive call on owners) ==>", ro;

} else if (a.region.World? && b.region.World?)  
 {
    print "cIM: world ",fmtobj(a), " and ", fmtobj(b), "    \n";
    printset(owners(a));  print " a<-->b ";  printset(owners(b)); print "\n";


} else {
    print "cIM: RETN owners don't match! \n";
    return false; 
 }

//RETUCSE ON FIELDSN!!!!!
//OI don't think we need to conisder the bit about recursion whenm i is_outside_signam/



 print "cIM: RETN a:",fmtobj(a)," o:",fmtobj(o)," ==> ",rv,"\n";
 return;
}



method {:TRUMP} printIsomorphicOWNED(a : Object, o : Object, m : Mapping, os : set<Object>)
  decreases os

  {
   print "(a in m) ", (a in m), "\n"; 
   if (a !in m) { return; }
   var b := m[a];
   print "a == b ", a == b, "\n";
   if (a == b) { return; }
   print "({a,b} <= os) ",({a,b} <= os),"\n";
   //print "(m[a] == b) ", (m[a] == b), "\n";
   print "(a.region.World? && b.region.World?) ", (a.region.World? && b.region.World?), "\n";
   print "(a.region.Heap? && b.region.Heap?) ", (a.region.Heap? && b.region.Heap?), "\n";   

   if ((a.region.Heap?) && (b.region.Heap?)) {
   print "(recurse on owner) ", isIsomorphicMappingOWNED(a.region.owner, o, m, os - {a,b}),"\n";
   }  

  print "Owners overall ", 
    (|| (a.region.World? && b.region.World?) 
     || ((a.region.Heap? && b.region.Heap?) && isIsomorphicMappingOWNED(a.region.owner, o, m, os - {a,b})))
  ,"\n";

  print "Field names ", (a.fields.Keys == b.fields.Keys), "\n";

  if (a.fields.Keys != b.fields.Keys) { 
      print "oops! a: ", a.fields.Keys,"\n";
      print "oops! b: ", b.fields.Keys,"\n";
      return; }

  var ns : seq<string> := set2seq(a.fields.Keys);

  for i := 0 to |ns| 
   {
    var n : string := ns[i];
    print "  ";
    print "a.",n," :=";
    printobj(a.fields[n]);
    print " - ";
    print "b.",n," :=";
    printobj(b.fields[n]);
    print "\n";

    print "   a.",n," in m ", a.fields[n] in m, "\n";
    if (a.fields[n] !in m) {return;}
    print "   ",n," in b.fields ", n in b.fields, "\n";
    if (n !in b.fields) {return;}
    print "   b.fields[",n,"] == m[a.fields[",n,"]] ",(b.fields[n] == m[a.fields[n]]) , "\n";
    print " (recurse on field ",n,") ", isIsomorphicMappingOWNED(a.fields[n], o, m, os - {a,b}),"\n";
   }
}

function {:onlyfans} fmtseqstr(ss : seq<string>) : string 
decreases ss
{
  if (|ss| == 0) then ("")
  else (if (|ss| == 1) then (ss[0])
  else (ss[0] + "," + fmtseqstr(ss[1..]))
  )
}



















// lemma {:timeLimit 15}  ValidReadSetBoundsEdges(os : set<Object>)  //bmmm
//   ensures OutgoingReferencesAreInTheseObjects(os) ==> (e2o(edges(os)) <= os)
//   ensures o2o(os) >= e2o(edges(os))
// {
//   assert (set e <- edges(os) :: e.f) <= os; 
//   assert forall o <- os ::  (set e <- edges({o}) :: e.t) <= o.outgoing();
//   assert forall o <- os ::  o.outgoing() <= (set o <- os, o2 <- o.outgoing() :: o2);

//   assert forall o <- os ::  o.outgoing() <= (set o <- os, o2 <- o.outgoing() :: o2);
  
//   assert forall o <- os :: (set e <- edges({o}) :: e.t)  <= (set o <- os, o2 <- o.outgoing() :: o2);
//   assert (set e <- edges(os) :: e.t) <= (set o <- os, o2 <- o.outgoing() :: o2);
// }


 //unforauntet we need a universe!
function ExpandingOutGetsAllOutgoings(os : set<Object>, U : set<Object>) : ( r : set<Object> )
  reads U
  requires OutgoingReferencesAreInTheseObjects(U)
  requires os <= U
  ensures  os <= r <= U
  ensures  OutgoingReferencesAreInTheseObjects(r)
  { U } // this is a cheat!!!


//needs a better name. 
//expands out an open heapwset into a cloed heapset (wnat bette words)
function o2o(os: set<Object>) : (rx : set<Object>) 
  reads os`fields
{
os + (set o <- os, o2 <- o.outgoing() :: o2) 
}



// lemma{:todo} InNOutBurger(es : set<Edge>) 
// {
// assert  
//     (var partition := partitionedIncomingEdges(es);
//        (forall o <- partition.Keys :: 
//       |(set e <- partition[o] | e.m.Owned? || e.m.Loaned? )| <= 1))
//    == 
//     (var partition := partitionedIncomingEdges(es);
//        (forall o <- partition.Keys :: 
//       |(set e <- partition[o] | e.m.Owned? || e.m.Loaned? )| <= 1));

// assert  //ERROR
//     (var partition := partitionedIncomingEdges(es);
//        (forall o <- partition.Keys :: 
//       |(set e <- partition[o] | FUCKEREDGE(e); e.m.Owned? || e.m.Loaned? )| <= 1))
//    == 
//     (var partition := partitionedIncomingEdges(es);
//        (forall o <- partition.Keys :: 
//       |(set e <- partition[o] | FUCKEREDGE(e); OwnedOrLoaned(e.m))| <= 1));

//   //ERROR
// assert  NoMoreThanOneIncomingEdges((m:Mode)=> true, es) == 
//     (var partition := partitionedIncomingEdges(es);
//        (forall o <- partition.Keys :: 
//       |(set e <- partition[o] |((m:Mode)=> true)(e.m)  )| <= 1));

//   //ERROR
// assert  NoMoreThanOneIncomingEdges(OwnedOrLoaned, es) == 
//     (var partition := partitionedIncomingEdges(es);
//        (forall o <- partition.Keys :: 
//       |(set e <- partition[o] | e.m.Owned? || e.m.Loaned? )| <= 1));


// assert  NoMoreThanOneIncomingEdges(OwnedOrLoaned, es) == 
//     (var partition := partitionedIncomingEdges(es);
//        (forall o <- partition.Keys :: 
//       |(set e <- partition[o] | OwnedOrLoaned(e.m) )| <= 1));

// }


// predicate OwnedOrLoaned(m : Mode) { m.Owned? || m.Loaned? }

// predicate BorrowedNotOwned(ms : set<Mode>) { 
//    (exists m <- ms :: m.Owned?) ==>  (forall m <- ms :: not(m.Borrow?)) }

// predicate BorrowsLoanedConsistentPermissions(ms : set<Mode>) {
//    forall m1 <- ms, m2 <- ms  
//         | (m1.Borrow? || m1.Loaned?) && (m2.Borrow? || m2.Loaned?)
//         :: m1.perm == m2.perm 
// }

// predicate WriteBorrow(m : Mode) { m.Borrow? && m.perm == Write }



///should these accept partitions - or sets, being individual partitions...
///todo would be better as sets, I think - 13 Jan 2024



    // causes an internal crash on 4.5.0.0
    // predicate OLDIncomingReferencesConstraintsOK( es : set<Edge> )
    //  reads set o <- e2o(es), o2 <- o.ValidReadSet() :: o2
    //  requires forall o <- e2o(es) :: o.Ready()
    //  requires forall o <- e2o(es) :: o.Valid() //hmm: 
    // { 
    //  var partition := partitionedIncomingEdges(es);

    //     //if there's an owning refrence, it had better be the only one
    //     ///could make exteral uniqueness just by adding in not(inside(e.f, e.t))}
    //  && (forall o <- partition.Keys :: 
    //   |(set e <- partition[o] | e.m.Owned? || e.m.Loaned? )| <= 1)
    //       //either Owned or Loaned, never both

    //  && (forall o <- partition.Keys :: 
    //   //  var modes := set pes <- partition[o] :: pes.m;
    //    (exists e <- partition[o] :: e.m.Borrow?) ==> 
    //       (forall e <- partition[o] :: not(e.m.Owned?)))
    //        //if there's a Borrow, there can't be an Owned reference

    //  && (forall o <- partition.Keys, e <- partition[o],  e' <- partition[o] 
    //     | (e.m.Borrow? || e.m.Loaned?) && (e'.m.Borrow? || e'.m.Loaned?)
    //     :: e.m.perm == e'.m.perm)
    //       // all Borrows and Loans must have the same permission.
          
    //  && (forall o <- partition.Keys :: 
    //     |(set e <- partition[o] | (e.m.Borrow? && e.m.perm == Write) :: e )| <= 1)
    //       //if there's a write borrow it must be the only one.


    // }

// lemma {:todo} {:here}  FewerEdgesStillValid(more : set<Edge>, less : set<Edge>) //fewer or less?
//     // reads set o <- e2o(more), o2 <- o.ValidReadSet() :: o2

//      requires less <= more

//      ensures e2o(less) <= e2o(more)
//      ensures (set o <- e2o(less), o2 <- o.ValidReadSet() :: o2) <= (set o <- e2o(more), o2 <- o.ValidReadSet() :: o2)

//      requires forall o <- e2o(more) :: o.Ready()
//      requires forall o <- e2o(more) :: o.Valid() //hmm: 
//      ensures  forall o <- e2o(less) :: o.Ready()
//      ensures  forall o <- e2o(less) :: o.Valid() //hmm: 

//      requires IncomingReferencesConstraintsOK(more)
//  //    ensures  IncomingReferencesConstraintsOK(less)
// {
//     e2oMonotonic(less,more);
//     var lesp := partitionedIncomingEdges(less);
//     var morp := partitionedIncomingEdges(more);

//     partitionedIncomingEdgesMonotonic(less, more, lesp, morp);
// }



//do i need thsi or if thingsa re disjoing is map + enough


//hmm doesn't help as much as I'd like
//reads  clauses policy
//by default - es => no reads clause
//os - think a bit.  reads os is a good start













method {:verify false} WalkiesMain() {

  print "Hello\n";
  
var t := new Object.frozen(protoTypes);
t.nick := "t";

//   t
//   a       b       c
//   d  e            f 
//  ij kl            g 
//                   h

assert t.Ready();

var a := new Object.make(protoTypes, t, {t}, "a");
assert AYY: AOK(a, {t,a});

var b := new Object.make(protoTypes, t, {t}, "b");
var c := new Object.make(protoTypes, t, {t}, "c");

assert CEE: AOK(c, {t,c});

var d := new Object.make(protoTypes, a, {a,t}, "d");

var e := new Object.make(protoTypes, a, {a,t}, "e");

var f := new Object.make(protoTypes, c, {t,a,c},     "f");

var g := new Object.make(protoTypes, f, {t,a,c,f},   "g");

var h := new Object.make(protoTypes, g, {t,a,c,f,g}, "h");

assert AOK(c, {t,c})  by { reveal CEE; }

var i := new Object.make(protoTypes, c, {t,a,d},     "i");
var j := new Object.make(protoTypes, c, {t,a,d},     "j");
var k := new Object.make(protoTypes, c, {t,a,e},     "i");
var l := new Object.make(protoTypes, c, {t,a,e},     "j");


assert t.Ready();

assert a.Ready();
assert b.Ready();
assert c.Ready();
assert d.Ready();
assert e.Ready();
assert f.Ready();
assert g.Ready();
assert h.Ready();
assert i.Ready();
assert j.Ready();
assert k.Ready();
assert l.Ready();

var os : set<Object> := {t,   a, b, c, d, e, f, g, h, i, j, k, l};

//b.fields := b.fields["fucker" := h];
// // b.fieldModes := b.fieldModes["fucker" := Rep];

AOKWiderContext(i, {t,a,d,i},  os);

i.fields := map["jat":= j]["dat":=d]["cat":= c]["rat":= a];

assert i.AllFieldsAreDeclared();
assert i.AllFieldsContentsConsistentWithTheirDeclaration();
assert i.AllOutgoingReferencesAreOwnership(os);
assert i.AllOutgoingReferencesWithinThisHeap(os);
assert AOK(i,os);

j.fields := map["nxt":= i];

k.fields := map["lat":= l]["dat":=d]["cat":= c]["rat":= a];
l.fields := map["nxt":= k];

d.fields := map["eye":=i];
e.fields := map["kye":=k];

assert AllOK(os, os);

print "done setup\n";

var isomap := map[d:=e,i:=k,j:=l,t:=t,a:=a,b:=b,c:=c];

var iddmap := map[d:=d,i:=i,j:=j,t:=t,a:=a,b:=b,c:=c];


// printobj(a);
// printobjfields(a);

// print "here edgeset\n";
assert forall o <- os :: o.Ready();
// printedgeset(edges(os));
// print "done edgeset\n\n";

// printobj(d); printobjfields(d);
// printobj(e); printobjfields(e);

// print d.region,"\n"; 
// print e.region,"\n";

// assert !d.region.World?;
// assert !e.region.World?;

//assert isIsomorphicMappingOWNED(d, d, isomap, os);

// print "ISO ISO ISO\n";

// var ros := walkies(d, d, isomap, os);

// return;

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

//////reveal Object.Ready();
assert t.AllOwnersAreWithinThisHeap(os);
assert a.AllOwnersAreWithinThisHeap(os);
assert b.AllOwnersAreWithinThisHeap(os);
assert c.AllOwnersAreWithinThisHeap(os);
assert d.AllOwnersAreWithinThisHeap(os);
assert e.AllOwnersAreWithinThisHeap(os);
assert f.AllOwnersAreWithinThisHeap(os);
assert g.AllOwnersAreWithinThisHeap(os);
assert h.AllOwnersAreWithinThisHeap(os);
assert i.AllOwnersAreWithinThisHeap(os);
assert j.AllOwnersAreWithinThisHeap(os);
assert k.AllOwnersAreWithinThisHeap(os);
assert l.AllOwnersAreWithinThisHeap(os);

assert forall o <- os :: (o.AllOwnersAreWithinThisHeap(os));

//print "walkiesClean CLEAN CLEAN CLEAN\n";
var tb, tm, ts := walkiesClean(c,c,map[],os,os);

print "+++++++++++++\n";
print "original store (os)\n";
print "+++++++++++++\n";
printobjectset(os);
print "+++++++++++++\n";
print "clones tm.Values - os\n";
print "+++++++++++++\n";
printobjectset(tm.Values - os);
print "+++++++++++++\n";
printmapping(tm);

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

var ok, kos :=  walkiesIsoOK(c, tb, c, tm, os);

print "walkes is ",ok,"\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

return; 

var dv, dos := walkiesIsoOK(d, e,  d, isomap, os);
print "%%%%% d to d ", dv, "\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

var ev, eos := walkiesIsoOK(d, d, d, iddmap, os);
print "%%%%% d to e ", ev, "\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

var av, aos := walkiesIsoOK(a, b, a, map[], os);
print "%%%%% a to b (nomap)", av, "\n";

av, aos := walkiesIsoOK(a, b, a, map[a:=b], os);
print "%%%%% a to b (partialmap)", av, "\n";

av, aos := walkiesIsoOK(a, b, a, map[a:=b,t:=t], os);
print "%%%%% a to b (fullmap)", av, "\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

var bv, bos := walkiesIsoOK(b, f, a, map[], os);
print "%%%%% b to f (nomap) ", bv, "\n";

bv, bos := walkiesIsoOK(b, f, a, map[b:=f,t:=c], os);
print "%%%%% b to f (map) ", bv, "\n";

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

return;

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";
print "d to e ", isIsomorphicMappingOWNED(d, d, isomap, os), "\n";
printmappingIsIsomorphic(isomap,d,os);
print "\n";
print "j to l ", isIsomorphicMappingOWNED(j, d, isomap, os), "\n";

printobject(i);
printobject(j);
printobject(k);
printobject(l);

print "\n////////////////////////////////////////////////////////////\nOBJECT d\n";
print "d to d ", isIsomorphicMappingOWNED(d, d, iddmap, os), "\n";


///////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////

print "\n////////////////////////////////////////////////////////////\nOBJECT d\n";
printobject(d);
print "OBJECT d.eye\n";
printobject(d.fields["eye"]);
print "////////////////////////////////////////////////////////////\nCLONE d -> dd\n";
var dd, mapdd, dddds := walkiesClean(d, d, map[], os, os); 
mapdd:= mapdd[t:=t];
printobject(dd);
print "\n////////////////////////////////////////////////////////////\nOBJECT dd\n";

//KJX - should track thisthrough5 the clone!!!
if ("eye" in dd.fields)  
    { printobject(dd.fields["eye"]); }
  else { print "FUCK FUCK eye missin\n"; }

print "////////////////////////////////////////////////////////////\nMAPPING d -> dd\n";
print isIsomorphicMappingOWNED(d, d, mapdd, os + mapdd.Values), "\n";
printmappingIsIsomorphic(mapdd, d, os + mapdd.Values);
printIsomorphicOWNED(d, d, mapdd, os + mapdd.Values);
print "////////////////////////////////////////////////////////////\n";
print "////////////////////////////////////////////////////////////\n";
print "////////////////////////////////////////////////////////////\n\n";
// printobject(dd);
// print "\n";
// printmapping(mapdd);
// print "\n\n";
// printobject(i);

// print "\n";
return;
print "\n////////////////////////////////////////////////////////////\nOBJECT i\n";
printobject(i);
print "////////////////////////////////////////////////////////////\nOBJECT ii\n";
var ii, mapii, iiiis := walkiesClean(i, i, map[], os, os);
printobject(ii);
print "////////////////////////////////////////////////////////////\nMAPPING i -> ii\n";
print isIsomorphicMappingOWNED(i, i, mapii, os + mapii.Values), "\n";
printmapping(mapii);
printIsomorphicOWNED(i, i, mapii, os + mapii.Values);
print "////////////////////////////////////////////////////////////\n";
print "////////////////////////////////////////////////////////////\n";
print "////////////////////////////////////////////////////////////\n\n";
// printobject(ii);
// print "\n";
// printmapping(mapii);

return;

print "about to ISO\n";

print "ISOMORPH2:tt:", isIsomorphicMappingOWNED(t, t, map[ d:= d,a:=a,t:=t], os),"\n";
print "ISOMORPH2:aa:", isIsomorphicMappingOWNED(a, a, map[ d:= d,a:=a,t:=t], os),"\n";

print "ISOMORPH1:de:", isIsomorphicMappingOWNED(d, d, map[ d:= e], os),"\n";
print "ISOMORPH2:dd:", isIsomorphicMappingOWNED(d, d, map[ d:= d], os),"\n";

print "ISOMORPH1:de:", isIsomorphicMappingOWNED(d, d, map[ d:= e,a:=a,t:=t], os),"\n";
print "ISOMORPH2:dd:", isIsomorphicMappingOWNED(d, d, map[ d:= d,a:=a,t:=t], os),"\n";

print "t, t\n";
printIsomorphicOWNED(t, t, map[ d:= e,a:=a,t:=t], os);

print "a, a\n";
printIsomorphicOWNED(a, a, map[ d:= e,a:=a,t:=t], os);


print "d, e\n";
printIsomorphicOWNED(d, d, map[ d:= e,a:=a,t:=t], os);
print "e, e\n";
printIsomorphicOWNED(d, d, map[ d:= d,a:=a,t:=t], os);

print "d, e\n";
printIsomorphicOWNED(d, d, map[ d:= e], os);
print "e, e\n";
printIsomorphicOWNED(d, d, map[ d:= d], os);

var oq : seq<Object> := [t,   a, b, c, d, e, f, g, h, i, j, k, l ];

assert forall o <- oq :: o.Ready();

  for i := 0 to |oq|
    {
      var o : Object := oq[i];

      assert o.Ready();

      print "\n=============================================================\n";
      print "=============================================================\n";

      printobject(o);
    }
   print "\n\n";

      for i := 0 to |oq|
       {
         printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then "i" else " ");
         print " ";
}
         print "\n";

       } 
  print "\n\n";

      for i := 0 to |oq|
       {
         printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then (oq[i].nick+oq[j].nick) else "  ");
         print " ";
}
         print "\n";

       } 
  print "\n\n";

  print "\n[\n";

      for i := 0 to |oq|
       {
         print "\"";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then ("x") else " ");
}
         if (i < (|oq|-1))  { print "\",\n";} else { print "\"\n";}

       }
print "]\n";





var matrix : seq<string>:= [
"x        ",
"xx       ",
"x x      ",
"x  x     ", 
"xx  x    ",
"xx   x   ",
"x  x  x  ",
"x  x  xx ",
"x  x  xxx"
];

  print "\n\n";

      for i := 0 to |matrix|
       {
         for j := 0 to |matrix[0]|
          {
         print match (inside(oq[i],oq[j]), (matrix[i][j]) )
           case (true,  'x') => "x"
           case (true,  ' ') => "M"  //missing
           case (false, ' ') => " "
           case (false, 'x') => "F"; //false posiutive, ie FUCKED
          }
         print "\n";
       }
print "\n";


print "\nDone\n\n";

var inverted := partitionedIncomingEdges(edges(os));

print inverted, "\n";

printedgemap(inverted);

print "\n\nHxR\n";

var hxr := HxR(edges(os));

print hxr,"\n\n"; 

print "\nDone\n";
} 
// end



method makeObjectSROF(s : string) returns (nu : Object) 
  ensures nu.region == World
  ensures fresh(nu)
  ensures nu.Ready()
  ensures nu.AMFO == {}
  ensures nu.fields.Values  == {}
  ensures nu.fieldModes == protoTypes
  ensures  nu.Ready()
  ensures  nu.AMFO <= nu.AMFO
  ensures  nu.AllOwnersAreWithinThisHeap(nu.AMFO)
  ensures  nu.fields == map[]
  ensures  nu.AllOutgoingReferencesAreOwnership(nu.AMFO)
  ensures  nu.AllOutgoingReferencesWithinThisHeap(nu.AMFO)
  ensures  nu.OwnersValid()
  ensures  nu.Valid()
  ensures  nu.TRUMP()
  ensures  nu.MOGO()
  modifies {}
{
 ////////reveal Object.Ready();
 nu := new Object.frozen(protoTypes);
 assert nu.MOGO();
 nu.nick := s;
 //////reveal nu.MAGA(); //////reveal nu.TRUMP(); //////reveal nu.Ready(); //////reveal nu.MOGO();
 assert nu.MOGO();
}


// lemma NickDontFuckWitMaMOGO(a : Object, b : Object) 
//   requires a.region == b.region
//   requires a.fields == b.fields
//   requires a.fields.Values == b.fields.Values
//   requires a.fieldModes == b.fieldModes
//   requires a.AMFO == b.AMFO
//   requires a.ValidReadSet() == b.ValidReadSet()

//   requires a.OwnersValid()
//   requires a.AllFieldsAreDeclared()
//   requires a.AllFieldsContentsConsistentWithTheirDeclaration()

//   requires a.Ready()
//   requires a.OwnersValid()
//   requires a.Valid()
//   requires a.TRUMP()
//   requires a.MOGO()

//   ensures  b.Ready()
//   ensures  b.OwnersValid()
//   ensures  b.AllFieldsAreDeclared()
//   ensures  b.AllFieldsContentsConsistentWithTheirDeclaration()

//   ensures  b.Valid()
//   ensures  b.TRUMP()
//   ensures  b.MOGO()


// {
//   //////reveal a.Ready(); 
//   //////reveal a.TRUMP();
//   //////reveal a.MOGO();

// assert forall n <- a.fields :: AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);

// }



twostate predicate  NickDontFuckWitMaMOGO(o : Object) 
  reads o`fields, o`fieldModes, o.AMFO
  reads (o.ValidReadSet() - {o})
{ 
   //&& o.region == old(o.region)
   && o.fields == old(o.fields)
   && o.fields.Values == old(o.fields.Values)
   && o.fieldModes == old(o.fieldModes)
   //&& o.AMFO == old(o.AMFO)
   && o.ValidReadSet() ==old(o.ValidReadSet())


  // //////reveal o.Ready(); 
  // //////reveal o.TRUMP();
  // //////reveal o.MOGO();

// assert forall n <- a.fields :: AssignmentCompatible(a, a.fieldModes[n], a.fields[n]);

}














method  {:verify false} makeObjectSROO(s : string, oo : Object) returns (nu : Object) 
  requires oo.MOGO()
  requires oo.Ready() && oo.Valid() && oo.TRUMP()

  ensures  nu.region == Heap(oo)
  ensures  fresh(nu)
  ensures  nu.fieldModes == protoTypes  
  ensures  nu.fields  == map[]
  ensures  nu.AMFO == oo.AMFO + {oo}
  ensures  nu !in nu.AMFO
  ensures  nu.Ready()
  ensures  nu.AMFO <= nu.AMFO
  ensures  nu.AllOwnersAreWithinThisHeap(nu.AMFO)
  ensures  nu.fields == map[]
  ensures  nu.AllOutgoingReferencesAreOwnership(nu.AMFO)
  ensures  nu.AllOutgoingReferencesWithinThisHeap(nu.AMFO)
  ensures  nu.OwnersValid()
  ensures  nu.Valid()
  ensures  nu.TRUMP()
  ensures  nu.MOGO()

  modifies {}
{
label start:

      //////reveal oo.Ready(), oo.TRUMP(), oo.MAGA(), oo.SUPERMAGA(), oo.MOGO();

  var ooHEAP := {oo} + oo.AMFO;

      assert oo.MOGO();
      assert oo.MAGA(ooHEAP);
      assert ooMAGA: oo.MAGA(ooHEAP);
      assert forall o <- (ooHEAP) :: o.TRUMP(); 

      assert  oo.Ready();
      assert  oo.AMFO <= oo.AMFO;
      assert  oo.AllOwnersAreWithinThisHeap(oo.AMFO);
      assert  oo.fields.Values <= (ooHEAP);
      assert  oo.AllOutgoingReferencesAreOwnership(ooHEAP);
      assert  oo.AllOutgoingReferencesWithinThisHeap(ooHEAP);
      assert  oo.OwnersValid();
      assert  oo.Valid();
      assert  oo.TRUMP();
      assert  oo.MOGO();



  nu := new Object.make(protoTypes, oo, {oo}+oo.AMFO, s);

      assert fresh(nu);
      assert nu.MOGO();
      assert nu != oo;
      assert nu.fields == map[];

  var nuHEAP := {nu} + nu.AMFO;
  assert nuHEAM: nuHEAP == {nu} + nu.AMFO;

      assert nuHEAP == {nu} + ooHEAP;
      assert nu.MAGA(nuHEAP);
      assert forall o <- (nuHEAP) :: o.TRUMP(); 

      assert  nu.Ready();
      assert  nu.AMFO <= nu.AMFO;
      assert  nu.AllOwnersAreWithinThisHeap(nu.AMFO);
      assert  nu.fields == map[];
      assert  nu.AllOutgoingReferencesAreOwnership(nuHEAP);
      assert  nu.AllOutgoingReferencesWithinThisHeap(nuHEAP);
      assert  nu.OwnersValid();
      assert  nu.Valid();
      assert  nu.TRUMP();
      assert  nu.MOGO();

  label before:

assert oo.MOGO();
  // assert fresh(nu);
  // nu.nick := s;
  // assert fresh(nu);

label after:
assert oo.MOGO(); 

// assert oo.MOGO() by {

// var a  := nu;
// var b  := oo;
// var bb := {oo} + oo.AMFO;

//      assert b.MOGO();
//      assert bb == {b} + b.AMFO;

//      assert forall o <- bb :: o.TRUMP();
//      //assert b.SUPERMAGA(bb,bb) //== b.MAGA(bb)

//      assert a.region.Heap?;
//      assert a.region.owner == b;
//      assert a.TRUMP();
//      assert a.deTRUMP(a).Ready();
//      assert a.fields == map[];
//      assert a.AllOwnersAreWithinThisHeap(bb); //that's the clever-ish bit
//      assert a.AllOwnersAreWithinThisHeap(a.AMFO);  //that's the clever-ish bit
//      //assert a.AMFO == bb  //should be derived!
// //     assert a.SUPERMAGA({a},{a}+bb);

//      nu.MAGAMonotonic4(a,b,bb);
// }

// assert oo.MOGO();

  assert unchanged@before(oo);
  assert unchanged@before(nu.AMFO);
  assert unchanged@before(oo.AMFO);
  assert unchanged@before(nu`fields,nu`fieldModes);
  assert unchanged@before(ooHEAP);


//   assert forall o : Object :: old(allocated(o)) ==> unchanged(o);

//   assert old@before(oo.MAGA(ooHEAP)) by { //////reveal ooMAGA; } 
// //  assert old@before(oo.MAGA(ooHEAP)) == oo.MAGA(ooHEAP);



  assert nuHEAP == ooHEAP + {nu};
  assert nuHEAP > ooHEAP;
  
  assert nu.fields == map[];  //thiese two shouild be trivial! 
  assert nu.deTRUMP(nu).AllOutgoingReferencesAreOwnership(nuHEAP) by {  assert nu.fields == map[];    }
  assert nu.AllOutgoingReferencesWithinThisHeap(nuHEAP) by { assert nu.fields == map[];    }

  assert nu.AllOwnersAreWithinThisHeap(nuHEAP) by 
  {
    assert nuHEAP == {nu} + nu.AMFO by { //////reveal nuHEAP; 
    }
    assert nuHEAP > nu.AMFO;
    assert forall oo <- nu.AMFO :: oo in nuHEAP;
    assert nu.AllOwnersAreWithinThisHeap(nuHEAP);
  }


  assert (forall o <- (nuHEAP) :: (o.TRUMP()));
  assert (forall o <- (nuHEAP) :: (o.deTRUMP(o).AllOutgoingReferencesAreOwnership(nuHEAP)));

  assert (forall o <- (nuHEAP) :: (o.AllOutgoingReferencesWithinThisHeap(nuHEAP)))
     by { 
          //////reveal ooMAGA;
          assert oo.MOGO();
          assert oo.MAGA(ooHEAP);
          assert (forall o <- (ooHEAP) :: (o.AllOutgoingReferencesWithinThisHeap(ooHEAP)));
          assert nuHEAP >= ooHEAP;
          assert forall o <- ooHEAP :: o in nuHEAP;
          assert forall o <- ooHEAP :: (o.AllOutgoingReferencesWithinThisHeap(ooHEAP));
          assert forall o <- ooHEAP :: (o.AllOutgoingReferencesWithinThisHeap(nuHEAP));
          assert nuHEAP - ooHEAP == {nu};
          assert nu.fields == map[];
          assert (nu.AllOutgoingReferencesWithinThisHeap(nuHEAP));
          assert forall o <- nuHEAP :: o.AllOutgoingReferencesWithinThisHeap(nuHEAP);

    }

  // assert (forall o <- (nuHEAP) :: ( && |o.fields.Keys| == 0
  //                               && o.AllOutgoingReferencesWithinThisHeap(nuHEAP)));
  // assert (forall o <- (nuHEAP) :: ( && o.AllOwnersAreWithinThisHeap(nuHEAP)
  //                               && (o.AMFO <= nuHEAP)      
  //                               && o.AllOwnersAreWithinThisHeap(oo.AMFO)));            



  assert old@before(nu.MOGO());

  assert NickDontFuckWitMaMOGO@before(nu);


  assert nu.OwnersValid();
  assert nu.Ready();
  assert nu.AllFieldsAreDeclared();
  assert nu.AllFieldsContentsConsistentWithTheirDeclaration();
  assert nu.Valid();
  assert nu.TRUMP();

assert forall o <- (nuHEAP) :: o.TRUMP();
  assert nu.deTRUMP(nu).AllOutgoingReferencesAreOwnership(nuHEAP);
  assert nu.AllOutgoingReferencesWithinThisHeap(nuHEAP);
  assert nu.AllOwnersAreWithinThisHeap(nuHEAP);

  assert nu.MAGA({nu} + nu.AMFO);

 // assert nu.MOGO();



 assert nu.MOGO() by 
  {
    //assert forall o : object :: old(allocated(o)) ==> unchanged(o);
    assert old@after(nu.MOGO());
    assert old@start(oo.MOGO());   
    assert nu != oo;
    assert nu !in nu.AMFO;
    assert nu !in oo.AMFO;
    assert nu.MOGO();
  }

// assert nu.MOGO(); 

// assert //Ready()inlined
//   && (nu.region.Heap?  ==> (nu.AMFO == nu.region.owner.AMFO + {nu.region.owner}))
//   && (nu.region.Heap?  ==> (nu.AMFO > nu.region.owner.AMFO))
//   && (nu.region.Heap?  ==> nu.region.owner.Ready())
//   && (nu.region.Heap?  ==> (forall owner <- nu.region.owner.AMFO :: nu.AMFO > owner.AMFO))
//   && (nu.region.Heap?  ==> (forall owner <- nu.region.owner.AMFO :: owner.Ready()))
//   && (forall owner <- nu.AMFO :: nu.AMFO > owner.AMFO)
//   && (forall owner <- nu.AMFO :: owner.Ready())
//   ;

 assert nu.MOGO(); 
//  assert nu.MAGA({nu} + nu.AMFO);

}







function fmtobj(o : Object) : string 
   reads o
{
  "Obj(" + o.nick + ")"
}

method printobj(o : Object) 
  ensures unchanged(o)
  modifies {}
{
 print "Obj(", o.nick, ")";
}


//should alos print field modes?
method printobjfields(o : Object)
{
  var t := o.fields;
  while t != map[]
    decreases t
  {
    var y: string;
    y :| y in t.Keys;
    print " ";
    print y,":=";
    printobj(t[y]);
    t := t - {y};
    print "\n";
  }
}

method {:onlyClone} printmapping(m: Mapping)
  modifies {}
  ensures unchanged(m.Keys,m.Values)
{
  var t := m;
  while t != map[]
    decreases t
  {
    var y: Object;
    y :| y in t.Keys;
    print " ";
    printobj(y); 
    print ":=";
    printobj(t[y]);
    t := t - {y};
    print "\n";
  }
}



method printmappingIsIsomorphic(m: Mapping, o : Object, os : set<Object>)
{
  var t := m;
  while t != map[]
    decreases t
  {
    var y: Object;
    y :| y in t.Keys;
    print " ";
    printobj(y); 
    print ":=";
    printobj(t[y]);
    print "  ";
    print isIsomorphicMappingOWNED(y, o, m, os);
    print "\n";
    t := t - {y};
   }
}




method printobject(o : Object) 
{
      printobj(o);
      print "\n  ";
      printset(owners(o));
      print "\n";
      printobjfields(o);
}

method printset(s : set<Object>) 
{
  var t := s;
  while t != {}
    decreases t
  {
    var y: Object;
    y :| y in t;
    printobj(y);
    print " ";
    t := t - {y};
  }
}


method printobjectset(s : set<Object>) 
{
  var t := s;
  while t != {}
    decreases t
  { 
    var y: Object;
    y :| y in t;
    printobject(y);
    print "- - - - - - - -\n";
    t := t - {y};
  }
}


method printedgeset(s : set<Edge>) 
{
  var t := s;
  while t != {}
    decreases t
  {
    var y: Edge;
    y :| y in t;
    print y, "  ";
    t := t - {y};
  }
}


method printedgemap(m : Incoming) 
{
  var t := m;
  while t != map[]
    decreases t
  {
    var y: Object;
    y :| y in t.Keys;
    printobj(y);
    print (|t[y]|);
    print ":= ";
    printedgeset(t[y]);
    t := t - {y};
    print "\n";
  }
}








//see also MapPlusKeyValue which is pretty siumilar
//but enforfes injuection  (mp[a] == mp[b] ==> a == b)
//maintian MapOK is nopt trivial

method {:onlyHURRAY} HURRAY_DAFNY( rm : map<Object,Object>, a : Object, b : Object, context : set<Object>) returns (m: map<Object,Object>)
   requires a !in rm.Keys
   requires b !in rm.Values //is this right? (this map, unlike fields, is injective)
   requires AOK(a,context)
   requires rm.Keys <= context
   requires MapOK(rm)
   requires AllOK(context)
   requires AllOK(rm.Values, context + rm.Values)
   requires AOK(b, context + rm.Values + {b})

   //maintaing MapOK
   requires forall oo <- (a.AMFO - {a}) :: oo in rm.Keys
   requires a.region.Heap? == b.region.Heap?
   requires a.region.Heap? ==> a.region.owner in a.AMFO
   requires a.region.Heap? ==> a.region.owner in rm.Keys //redundant...

   requires  a.region.Heap? ==> rm[a.region.owner] == b.region.owner
   
   requires forall oo <- (a.AMFO - {a}) :: rm[oo] in b.AMFO

   ensures  m == rm[a:=b]
   ensures  a in m.Keys
   ensures  m.Keys == rm.Keys + {a}
   ensures  m.Values == rm.Values + {b}
   ensures  m[a] == b
   ensures  forall x <- rm :: m[x] == rm[x]

   ensures  unchanged(context)
   ensures  AllOK(context)
   ensures  MapOK(m) 
   ensures  AllOK(m.Values, context + m.Values)
   ensures  mapLEQ(rm, m)
{  
    assert  AllOK(rm.Values, context + rm.Values);
    AllOKWiderContext(rm.Values, context + rm.Values, {b});
    assert  AOK(b, context + rm.Values + {b});
    AllOKWiderFocus(rm.Values, {b}, context + rm.Values + {b} );
    assert AllOK(rm.Values + {b}, context + rm.Values + {b});

    m := rm[a:=b];
    assert m.Keys == rm.Keys + {a};
    assert m.Values == rm.Values + {b};
    //arseume m.Values == rm.Values + {b};
    assert context + rm.Values + {b} == context + m.Values;
    assert AOK(b, context + m.Values);
    assert AllOK(m.Values, context + m.Values);

    assert forall x <- rm.Keys :: m[x] == rm[x];
    assert forall x <- m.Keys :: 
        if (x == a) then (m[x] == b) else (m[x] == rm[x]);

///MapOK(m):

  assert (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?);
  assert (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO);
  assert (forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys);
  assert (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys);
  assert (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner );

  assert forall oo <- (a.AMFO - {a}) :: oo in rm.Keys;
  assert forall oo <- (a.AMFO - {a}) :: oo in m.Keys;

  assert forall oo <- (a.AMFO - {a}) :: rm[oo] in b.AMFO;  //requires
  assert forall oo <- (a.AMFO - {a}) :: m[oo] in b.AMFO;   //nearly
    assert m[a] == b;
  assert forall oo <- a.AMFO :: 
        if (oo == a) then (m[oo] == b) else (m[oo] == rm[oo]);

  assert forall oo <- (a.AMFO - {a}) :: rm[oo] in b.AMFO;
  assert forall oo <- (a.AMFO - {a}) :: m[oo] in b.AMFO;

assert AOK(a,context);
assert a.Valid();
assert a.OwnersValid();
assert a !in a.AMFO;
assert a.AMFO == (a.AMFO - {a});
assert forall oo <- (a.AMFO) :: m[oo] in b.AMFO;
}






function {:verify false} F_DAF( rm : map<Object,Object>, a : Object, b : Object, context : set<Object>) : (m : map<Object,Object>)
   reads a, b, context, rm.Keys, rm.Values
   requires a !in rm.Keys
   requires b !in rm.Values //is this right? (this map, unlike fields, is injective)
   requires AOK(a,context)
   requires rm.Keys <= context
   requires MapOK(rm)
   requires AllOK(context)
   requires AllOK(rm.Values, context + rm.Values)
   requires AOK(b, context + rm.Values + {b})



   ensures  m == rm[a:=b]
   ensures  a in m.Keys
   ensures  m.Keys == rm.Keys + {a}
   ensures  m.Values == rm.Values + {b}
   ensures  m[a] == b
   ensures  forall x <- rm :: m[x] == rm[x]

   //ensures  unchanged(context)
   ensures  AllOK(context)
   ensures  MapOK(m) 
   ensures  AllOK(m.Values, context + m.Values)
   ensures  mapLEQ(rm, m)
{  
    assert  AllOK(rm.Values, context + rm.Values);
    AllOKWiderContext(rm.Values, context + rm.Values, {b});
    assert  AOK(b, context + rm.Values + {b});
    AllOKWiderFocus(rm.Values, {b}, context + rm.Values + {b} );
    assert AllOK(rm.Values + {b}, context + rm.Values + {b});

    var m := rm[a:=b];
    assert m.Keys == rm.Keys + {a};
    assert m.Values == rm.Values + {b};
    //arseume m.Values == rm.Values + {b};
    assert context + rm.Values + {b} == context + m.Values;
    assert AOK(b, context + m.Values);
    assert AllOK(m.Values, context + m.Values);

    assert forall x <- rm.Keys :: m[x] == rm[x];
    assert forall x <- m.Keys :: 
        if (x == a) then (m[x] == b) else (m[x] == rm[x]);

///MapOK(m):

  assert (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?);
  assert (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO);
  assert (forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys);
  assert (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys);
  assert (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner );

  assert forall oo <- (a.AMFO - {a}) :: oo in rm.Keys;
  assert forall oo <- (a.AMFO - {a}) :: oo in m.Keys;

  assert forall oo <- (a.AMFO - {a}) :: rm[oo] in b.AMFO;  //requires
  assert forall oo <- (a.AMFO - {a}) :: m[oo] in b.AMFO;   //nearly
    assert m[a] == b;
  assert forall oo <- a.AMFO :: 
        if (oo == a) then (m[oo] == b) else (m[oo] == rm[oo]);

  assert forall oo <- (a.AMFO - {a}) :: rm[oo] in b.AMFO;
  assert forall oo <- (a.AMFO - {a}) :: m[oo] in b.AMFO;

assert AOK(a,context);
assert a.Valid();
assert a.OwnersValid();
assert a !in a.AMFO;
assert a.AMFO == (a.AMFO - {a});

  // if (a in a.AMFO) {
  //   assert m[a] == b;
  //   assert b in b.AMFO;
  //   assert a.AMFO ==  (a.AMFO - {a}) + {a};
  // } else { 
  //   assert a.AMFO == (a.AMFO - {a});
  // }
  assert forall oo <- (a.AMFO) :: m[oo] in b.AMFO;

  // forall x <- m.Keys, oo <- x.AMFO 
  //   ensures (m[oo] in m[x].AMFO) 
  //     {
  //       if (x in rm.Keys) { assert (rm[oo] in rm[x].AMFO); 
  //                           assert (m[oo] in m[x].AMFO); 
  //       } else { 
  //         assert x == a;
  //         assert forall oo <- a.AMFO :: oo in rm.Keys;
  //         assert forall oo <- (a.AMFO + {a}) :: rm[oo] in rm.Values;
  //       }
  //     }

      m
   }










method  {:onlyFUCKED} FUCKA( rm : map<Object,Object>, a : Object, b : Object, context : set<Object>) returns (m : map<Object,Object>)
   requires a !in rm.Keys

   requires a !in rm.Keys
   requires b !in rm.Values //is this right? (this map, unlike fields, is injective)

   requires rm.Keys <= context
   requires MapOK(rm)
   requires AllOK(context)
   requires AllOK(rm.Values, context + rm.Values)
   requires AOK(b, context + rm.Values)

   //maintaing MapOK
   requires forall oo <- a.AMFO :: oo in rm.Keys
   requires a.region.Heap? == b.region.Heap?
   requires a.region.Heap? ==> a.region.owner in a.AMFO
   requires a.region.Heap? ==> a.region.owner in rm.Keys //redundant...

   requires  a.region.Heap? ==> rm[a.region.owner] == b.region.owner
   
   requires forall oo <- a.AMFO :: rm[oo] in b.AMFO



   ensures  a in m.Keys
   ensures  m.Keys == rm.Keys + {a}
   ensures  m.Values == rm.Values + {b}



{  
        m := rm[a:=b];
        //assert m.Values == rm.Values + {b};
}

// predicate MapOK(m : Mapping)
// {
//   && (forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys)
//   && (forall x <- m.Keys :: x.region.Heap? == m[x].region.Heap?)
//   && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO)
//   && (forall x <- m.Keys |  x.region.Heap? :: x.region.owner in m.Keys)
//   && (forall x <- m.Keys |  x.region.Heap? :: m[x.region.owner] == m[x].region.owner )
//   && (forall x <- m.Keys, oo <- x.AMFO :: m[oo] in m[x].AMFO)
// //  && forall x <- m.Keys :: (not(inside(x,o)) ==> (m[x] == x))
// }



function {:onleee} id<T>(x : T) : T {x}

function variant() : ( set<Object>, set<(Object,Object)>, set<(Object,string)>)
{
  ({}, {}, {})
}





//   assert rv.ns !! rv.oHeap by {
//     reveal valid();
//     assert ns !! oHeap;
//     assert  v !in (oHeap + ns);
//     assert ns + {v} !! oHeap;
//     assert rv.oHeap == oHeap;
//     assert rv.ns == ns + {v};
//     assert rv.ns !! rv.oHeap;
//   }

//   assert rv.vs <= rv.ns + rv.oHeap by {
//      assert vs <= ns + oHeap;
//      assert rv.vs == vs + {v};
//      assert rv.ns == ns + {v};
//      assert rv.oHeap == oHeap;
//      assert (vs + {v}) <=  ns + {v} + oHeap;
//      assert rv.vs <= rv.ns + rv.oHeap;
//   }
//   assert AOK(rv.o, rv.oHeap);
//   assert AllOK(rv.oHeap);
//   assert AllOK(rv.ks, rv.oHeap);
//   assert AllOK(rv.vs, rv.oHeap+rv.ns) by {
//       assert v !in (oHeap + ns);
//       assert AOK(v, oHeap+ns+{v});
//       assert AllOK(vs, oHeap+ns);
//       AllOKWiderContext(vs, oHeap+ns, {v});
//       AllOKWiderFocus(vs, {v}, oHeap+ns+{v});  
//       assert AllOK(vs+{v}, oHeap+ns+{v});

//       assert rv.vs == vs+{v};
//       assert rv.ns == ns+{v};
//       assert oHeap+ns+{v} ==  rv.oHeap+rv.ns;
//       assert AllOK(rv.vs, rv.oHeap+rv.ns);
//   }
//   assert AllOK(rv.ns, rv.oHeap+rv.ns);
//   assert MapOK(rv.m);
//   // assert (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
//   // assert (forall x <- rv.ks, oo <- x.AMFO:: rv.m[oo] in rv.m[x].AMFO);
//   assert (forall x <- rv.ks :: AreWeNotMen(x, rv));

//     //  if (inside(x,rv.o))
//     //    then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//     //    else (rv.m[x] == x));

// reveal valid();
// assert rv.valid();
//       rv}

    // opaque function {:onlyO} putOutside(k : Object) : (r : Map)
    //   //put k -> k into map
    //   reads oHeap`fields, oHeap`fieldModes
    //   reads ns`fields, ns`fieldModes
    //   requires valid()
    //   requires k !in ks
    //   requires k in oHeap4
    //   requires k !in vs
    //   requires not(inside(k, o))
    //   ensures  r == Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns)
    //   ensures  r.valid()
    //   { 
    //     var rv := Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns);
    //     reveal rv.valid(); assert rv.valid();
    //     rv
    //   }


//    opaque function putAllOutside(js : set<Object>) : (r : Map)
//       //put k <- js :: k -> k into map, js oustide o
//       decreases js
//       reads oHeap`fields, oHeap`fieldModes
//       reads ns`fields, ns`fieldModes
//       requires calid()
//       requires js !! ks
//       requires js <= oHeap
//       requires CallOK(js, oHeap)
//       requires forall j <- js :: j.AMFO <= ks   //need to update - all my owners EXCEPT ME!
//       requires js !! vs
//       requires forall j <- js :: not(inside(j, o))

//       // ensures r == Map(m[k:=k], js+{k}, vs+{k}, o, oHeap, ns)
//       // ensures r.calid()
// {
//      if (|js| == 0) then (this) else 

//     //  var ts := js;
//     //  while ts != map[]
//     //    decreases ts
//     //    {
//     //      var y : Object
//     //     y :| y in ta.Keys;
//     //    }g

// //     var j :| j in js;

//      var jsq := set2seq(js);
//      var j := jsq[0];
  

//      assert CallOK(js, oHeap);
//      COKfromCallOK(j, js, oHeap);
//      assert COK(j,oHeap);
//      CallOKNarrowFocus(js - {j}, js, oHeap);
//      putOutside(j).putAllOutside(js - {j})
// }



//   method {:onlyAndTheRest} putAllOutside(js : set<Object>) returns (r : Map)
//       //put k <- js :: k -> k into map, js oustide o
//       decreases js
//       // reads oHeap`fields, oHeap`fieldModes
//       // reads ns`fields, ns`fieldModes
//       //requires calid()
//       requires 
//          (&& calidObjects() 
//           && calidOK()
//           && calidMapAndTheRest(js))
//           // calidMap();

//       requires (js !! ks) && (js !! m.Keys)
//       requires js <= oHeap
//       requires CallOK(js, oHeap)
//       requires forall j <- js :: j.AMFO <= (ks+js)   //need to update - all my owners EXCEPT ME!
//       requires js !! vs
//       requires forall j <- js :: not(inside(j, o))

//       ensures  (js !! ks) && (js !! m.Keys)
//       ensures  r.m == (map x <- js :: x) + m
//       // ensures  r.m == Extend_A_Map(m, js)
//       // ensures  r == Map( Extend_A_Map(m, js), ks+js, vs+js, o, oHeap, ns)
//       ensures  r == Map(  (map x <- js :: x) + m, ks+js, vs+js, o, oHeap, ns)
//       ensures  r.calid()
// {

//      if (|js| == 0) {
//       assert this ==  Map( Extend_A_Map(m, {}), ks, vs, o, oHeap, ns);
//       return this;}

//     //  var ts := js;
//     //  while ts != map[]
//     //    decreases ts
//     //    {
//     //      var y : Object
//     //     y :| y in ta.Keys;
//     //    }g

//     var j :| j in js;

//     //  var jsq := set2seq(js);
//     //  var j := jsq[0];
  

//      assert CallOK(js, oHeap);
//      COKfromCallOK(j, js, oHeap);
//      assert COK(j,oHeap);
//      CallOKNarrowFocus(js - {j}, js, oHeap);
//      assert j.AMFO <= this.ks + (js - {j}) + {j};

//      var r1 := putOutsideAndTheRest(j, js - {j});
//      assert r1.ks == ks+{j};
//      assert r1.vs == vs+{j};
//      assert r1.o == o;
//      assert r1.oHeap == oHeap;
//      assert r1.ns == ns;
//      assert r1.m == Extend_A_Map(m, {j});
//      assert r1 ==  Map( Extend_A_Map(m, {j}), ks+{j}, vs+{j}, o, oHeap, ns);
//      var r2 := r1.putAllOutside(js - {j});
 
//   //   assert r2.m ==  Extend_A_Map(r1.m, (js - {j}));
//   //   assert r2 == Map( Extend_A_Map(r1.m, (js - {j})), ks+js, vs+js, o, oHeap, ns);
 
//      assert ({j} + (js - {j})) == js;
//      assert ((ks + {j}) + (js - {j})) == ks+js;
//      assert (ks+js) == ((ks + {j})+(js - {j}));
//      assert r2.ks == ks+js;
//      assert r2.vs == vs+js;
//      assert r2.o == o;
//      assert r2.oHeap == oHeap;
//      assert r2.ns == ns;
//      assert r2.ns == r1.ns;
//      assert r1.ns == ns;
//     //  assert r2.m == (map x <- (js-{j}):: x) + r1.m;
//     //  assert r2.m == Extend_A_Map(m, (js - {j}));
//      return r2;
// }



//     opaque function {:onlyAndTheRest} putOutsideAndTheRest(k : Object, rest : set<Object>) : (r : Map)
//       //put k -> k into map, k oustide o;  knowning rest wil be added later
//       reads oHeap`fields, oHeap`fieldModes
//       reads ns`fields, ns`fieldModes
//       //requires calid()
//       requires //calid() || 
//          (&& calidObjects() 
//           && calidOK()
//           && calidMapAndTheRest(rest) )
//           //&& calidSheep())
//       requires k !in ks
//       requires k in oHeap
//       requires COK(k, oHeap)
//       requires k.AMFO <= (ks + rest + {k})  //need to update - all my owners EXCEPT ME!
//       requires k !in vs
//       requires not(inside(k, o))

//       ensures r == Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns)
//       //ensures r.calid()
       
//       ensures r.calidObjects()
//       ensures r.calidOK()
//       ensures r.calidMapAndTheRest(rest)
//       { 
//       reveal calid(); 
//       reveal calidObjects(); //assert calidObjects();
//       reveal calidOK(); //assert calidOK();
//       reveal calidMapAndTheRest(); //assert calidMapAndTheRest(rest);

//       // assert calid() || 
//       //    (&& calidObjects() 
//       //     && calidOK()
//       //     && calidMapAndTheRest(rest));

//       assert calidObjects();
//       assert  calidOK();
//       assert  calidMapAndTheRest(rest);

//       var rv := Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns);

//         assert rv.calidObjects() by {
//             reveal rv.calidObjects();

//             assert rv.ks == rv.m.Keys;
//             assert rv.vs == rv.m.Values;
//             assert rv.o in rv.oHeap;
//             assert rv.ks <= rv.oHeap;
//             assert rv.ns !! rv.oHeap;
//             assert rv.vs <= rv.ns + oHeap;

//             assert rv.calidObjects(); 
//         }

//         assert k !in vs; // from reqs
//         assert vs == m.Values by { 
//             // assert calid();
//             // reveal calid();
//             assert calidObjects();
//             reveal calidObjects();
//             assert vs == m.Values;
//                    }
//         assert k !in m.Values;


//         assert rv.calidOK() by {
//             reveal rv.calidOK();
//             assert COK(rv.o, rv.oHeap);
//             assert CallOK(rv.oHeap);
//             CallOKfromCOK(k, oHeap);
//             assert CallOK(ks, oHeap);
//             CallOKtoSubset(ks, oHeap);
//             CallOKWiderFocus(ks, {k}, oHeap);
//             assert CallOK(rv.ks, rv.oHeap);
//             CallOKWiderContext({k}, oHeap, ns);
//             CallOKtoSubset(vs, oHeap+ns);
//             CallOKWiderFocus(vs, {k}, oHeap+ns);
//             assert CallOK(rv.vs, rv.oHeap+ns);
//             assert CallOK(rv.ns, rv.oHeap+ns);
//             reveal rv.calidOK(); assert rv.calidOK();
//           }


// //        reveal rv.calidMap();
// //        assert rv.calidMap() by {
//             reveal rv.calidMap();
//             reveal rv.calidMapAndTheRest();
//             assert MapOKAndTheRest(rv.m, rest) by {
//                 assert MapOKAndTheRest(m, rest);
//                 assert COK(k, oHeap);
//                 reveal COK();
//                 assert rv.ks == ks + {k};          
//                 assert rv.m.Keys == m.Keys + {k};

//                 reveal rv.calidObjects();
//                 assert rv.calidObjects();
//                 reveal calidObjects();
//                 assert calidObjects();

//                 assert rv.m.Keys == rv.ks;
//                 assert k.AMFO <= (ks + rest);

//                 assert forall x <- m.Keys :: x.AMFO <= (ks+rest) by { 
//                   assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys + rest;
//                 }  
//                 assert k.AMFO <= (ks + rest);
//                 assert forall x <- m.Keys+{k} :: x.AMFO <= (ks+{k}+rest);
//                 assert (ks+{k}) == m.Keys+{k} == rv.ks == rv.m.Keys;
//                 assert forall x <- rv.m.Keys :: x.AMFO <= (rv.m.Keys+rest);
//                 assert forall x <- rv.m.Keys, oo <- x.AMFO :: oo in (rv.m.Keys+rest);

//                 assert (forall x <- rv.m.Keys :: x.region.Heap? == rv.m[x].region.Heap?);
//                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO);
//                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in rv.m.Keys+rest);
//                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: 
//                       || (x.region.owner in rest)
//                       || (rv.m[x.region.owner] == rv.m[x].region.owner)
//                       );
//             }  //MAapOKAndTheRest
// //       }
//             assert (forall x <- rv.m.Keys :: (not(inside(x,rv.o)) ==> (rv.m[x] == x))) by 
//             {
//                   reveal rv.calidObjects();
//                   assert ks == m.Keys;
//                   assert rv.ks == rv.m.Keys;
//                   assert (forall x <- ks  :: (not(inside(x,o)) ==> (m[x] == x)));
//                   assert (forall x <- ks  :: (not(inside(x,o)) ==> (rv.m[x] == x)));
//                   assert rv.m[k] == k;
//                   assert (forall x <- {k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
//                   assert (forall x <- ks+{k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
//                   assert rv.ks == ks+{k};
//                   assert (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
//             }
//             reveal rv.calidObjects();
//             assert ks == m.Keys;
//             assert rv.ks == rv.m.Keys;
//             assert (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
//             assert (forall x <- rv.m.Keys, oo <- x.AMFO ::
//                           ((oo in rest) || rv.m[oo] in rv.m[x].AMFO));
//             assert (forall x <- ks, oo <- x.AMFO ::
//                           ((oo in rest) || m[oo] in m[x].AMFO));
//             reveal rv.calidMapAndTheRest();
//             assert rv.calidMapAndTheRest(rest);
      
//         reveal rv.calidSheep();
//             reveal rv.calidObjects();
//             assert ks == m.Keys;
//             assert rv.ks == rv.m.Keys;
//         assert not(inside(k, o));
//         reveal calidMapAndTheRest();
//         assert calidMapAndTheRest(rest);
//         // reveal calidSheep();
//         // assert calidSheep();

//       assert rv.ks == rv.m.Keys == (ks+{k});

//       reveal AreWeNotMen();
//       assert forall x <- rv.m.Keys :: 
//       &&      ((inside(x,rv.o)) ==> (rv.m[x] in rv.ns))
//       && ((not(inside(x,rv.o))) ==> (rv.m[x] == x));

//       assert forall x <- rv.m.Keys :: AreWeNotMen(x, this);


//       //  assert (forall x <- ks  :: inside(x, rv.o) ==> ((m[x] in rv.ns) && (UniqueMapEntry(m,x))));
//       //  assert (forall x <- {k} :: inside(x, rv.o) ==> ((m[x] in rv.ns) && (UniqueMapEntry(m,x))));



//       //  assert (forall x <- ks  :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))));
//       //  assert (forall x <- {k} :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))));




//       //  assert rv.m.Keys == ks + {k};
//       //  assert rv.m == m[k:=k];
//       //  assert (forall x <- ks+{k}    :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));
//       //  assert (forall x <- rv.m.Keys :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));
//       //  assert (forall x <- rv.m.Keys :: not(inside(x, rv.o)) ==> (rv.m[x] == x));

//       //  assert (forall x <- rv.m.Keys :: 
//       //    && (inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))))
//       //    && (not(inside(x, rv.o)) ==> (rv.m[x] == x)));
      
//       //  assert (forall x <- rv.m.Keys :: 
//       //   (&& (inside(x, rv.o) ==> ((rv.m[x] !in rv.ns) && (UniqueMapEntry(m,x))))
//       //    && (not(inside(x, rv.o)) ==> (rv.m[x] == x)))
//       //   ==>
//       //   (if (inside(x,rv.o))
//       //       then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//       //       else (rv.m[x] == x))
//     //    //  );

//     //    forall x <- rv.m.Keys ensures (
//     //       if (inside(x,rv.o))
//     //         then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//     //         else (rv.m[x] == x))
//     //   } { 
//     //     assert (inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));
//     //     assert (not(inside(x, rv.o)) ==> (rv.m[x] == x));

//     //     assert if (inside(x,rv.o))
//     //         then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//     //         else true;

//     //     assert if (not(inside(x,rv.o)))
//     //         then (rv.m[x] == x)
//     //         else true;

//     // assert if (inside(x,rv.o))
//     //         then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//     //         else (rv.m[x] == x);


//     //    }

//         assert calidSheep();
//         reveal rv.calidSheep();
//         //reveal UniqueMapEntry();

//         assert ks == m.Keys;
//         // assert (forall x <- ks |    (inside(x,o)) :: (m[x] in ns));
//         // assert (forall x <- ks |    (inside(x,o)) :: (UniqueMapEntry(m,x)));
//         // assert (forall x <- ks | not(inside(x,o)) :: (m[x] == x));

// reveal AreWeNotMen();  
// reveal UniqueMapEntry();
//         assert forall x <- ks  :: AreWeNotMen(x, this);
//         assert forall x <- {k} :: AreWeNotMen(x, rv);
//         assert forall x <- rv.m.Keys :: AreWeNotMen(x, rv);
      
//         assert rv.calidObjects() && rv.calidOK();
//         assert rv.calidMapAndTheRest(rest);
//         //  && rv.calidMap();
//         // assert rv.calidSheep();

//        // reveal rv.calid(); assert rv.calid();
//         rv
        
//    }



      // assert (forall x <- ks :: 
      //     if (inside(x,o))
      //       then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
      //       else (m[x] == x));

      //  assert (forall x <- ks        ::  not(inside(x,o)) ==> (m[x] == x));

      //  assert (forall x <- m.Keys    ::  not(inside(x, o)) ==> (m[x] == x)) by {
      //     assert NUKE: (forall x <- ks        ::  not(inside(x,o)) ==> (m[x] == x));
      //     assert (forall x <- m.Keys    ::  not(inside(x, o)) ==> (m[x] == x)) by 
      //        { 
      //     reveal calidObjects();
      //     assert ks == m.Keys;
      //     reveal NUKE;
      //     assert (forall x <- ks        ::  not(inside(x,o)) ==> (m[x] == x));
      //     assert (forall x <- m.Keys    ::  not(inside(x,o)) ==> (m[x] == x));
      //        }
      //  }
      //  assert not(inside(k,o));
      //  assert (forall x <- {k}       ::  not(inside(x, rv.o)) ==> (rv.m[x] == x)); 
      //  assert (forall x <- rv.m.Keys ::  not(inside(x, rv.o)) ==> (rv.m[x] == x));

      //  assert (forall x <- rv.m.Keys :: 
      //     not(inside(x, rv.o)) ==> (rv.m[x] == x));
      //  assert (forall x <- rv.m.Keys :: 
      //     inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));


  // assert (forall x <- rv.m.Keys | x in m.Keys :: 
  //         inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))));
// 
// 
// assert rv.ks == rv.m.Keys == (ks+{k});
//       //  assert (forall x <- ks  :: inside(x, rv.o) ==> ((m[x] in rv.ns) && (UniqueMapEntry(m,x))));
//       //  assert (forall x <- {k} :: inside(x, rv.o) ==> ((m[x] in rv.ns) && (UniqueMapEntry(m,x))));
// 
// 

      //  assert (forall x <- ks  :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))));
      //  assert (forall x <- {k} :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))));




      //  assert rv.m.Keys == ks + {k};
      //  assert rv.m == m[k:=k];
      //  assert (forall x <- ks+{k}    :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));
      //  assert (forall x <- rv.m.Keys :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));
      //  assert (forall x <- rv.m.Keys :: not(inside(x, rv.o)) ==> (rv.m[x] == x));

      //  assert (forall x <- rv.m.Keys :: 
      //    && (inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))))
      //    && (not(inside(x, rv.o)) ==> (rv.m[x] == x)));
      
      //  assert (forall x <- rv.m.Keys :: 
      //   (&& (inside(x, rv.o) ==> ((rv.m[x] !in rv.ns) && (UniqueMapEntry(m,x))))
      //    && (not(inside(x, rv.o)) ==> (rv.m[x] == x)))
      //   ==>
      //   (if (inside(x,rv.o))
      //       then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
      //       else (rv.m[x] == x))
    //    //  );

    //    forall x <- rv.m.Keys ensures (
    //       if (inside(x,rv.o))
    //         then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
    //         else (rv.m[x] == x))
    //   } { 
    //     assert (inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));
    //     assert (not(inside(x, rv.o)) ==> (rv.m[x] == x));

    //     assert if (inside(x,rv.o))
    //         then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
    //         else true;

    //     assert if (not(inside(x,rv.o)))
    //         then (rv.m[x] == x)
    //         else true;

    // assert if (inside(x,rv.o))
    //         then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
    //         else (rv.m[x] == x);


    //    }
// 
//         assert calidSheep();
//         reveal rv.calidSheep();
//         //reveal UniqueMapEntry();
// 
//         assert ks == m.Keys;
        // assert (forall x <- ks |    (inside(x,o)) :: (m[x] in ns));
        // assert (forall x <- ks |    (inside(x,o)) :: (UniqueMapEntry(m,x)));
        // assert (forall x <- ks | not(inside(x,o)) :: (m[x] == x));
// 
        // assert not(inside(k,o));
        // assert rv.m == m[k:=k];
        // assert rv.m[k] == k;
        // assert rv.o == o;
// 
        // assert (forall x <- {k} |    (inside(x,rv.o)) :: (rv.m[x] in rv.ns));
        // assert (forall x <- {k} |    (inside(x,rv.o)) :: (UniqueMapEntry(rv.m,x)));
        // assert (forall x <- {k} | not(inside(x,rv.o)) :: (rv.m[x] == x));
// 
        // assert rv.ks == rv.m.Keys == ks+{k};
        // assert (forall x <- rv.m.Keys | (inside(x,rv.o)) :: (rv.m[x] in rv.ns));
        // assert (forall x <- rv.m.Keys :: 
          // if (x == k) then (not(inside(x,rv.o))) 
            //  else ((x in m.Keys) && (rv.m[x] == m[x]) && 
                  // (inside(x,rv.o) ==> (UniqueMapEntry(rv.m,x))))); 
        
//        assert (forall x <- rv.m.Keys | not(inside(x,rv.o)) :: (rv.m[x] == x));



//     opaque function {:onlyNUKE} putOutside(k : Object) : (r : Map)
//       //put k -> k into map
//       //working as of Tuesday 11 June 2024
//       reads oHeap`fields, oHeap`fieldModes
//       reads ns`fields, ns`fieldModes
//       requires calid()
//       requires k !in ks
//       requires k in oHeap
//       requires COK(k, oHeap)
//       requires k.AMFO <= ks   ///HMMM<<
//       requires k !in vs
//       requires not(inside(k, o))
//       ensures r.calid()
//       // ensures  r == Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns)
//       // ensures  (var rv := r; 
//       //              reveal rv.valid(); assert rv.valid(); arseume r.valid(); r.valid() )
//       { 
//         reveal calid(); assert calid();
//         var rv := Map(m[k:=k], ks+{k}, vs+{k}, o, oHeap, ns);

//         //this
//         //var rv := Map(m, ks, vs, o, oHeap, ns);

//        //reveal rv.calidObjects();    
//         assert rv.calidObjects() by {
//             reveal rv.calidObjects();

//             assert rv.ks == rv.m.Keys;
//             assert rv.vs == rv.m.Values;
//             assert rv.o in rv.oHeap;
//             assert rv.ks <= rv.oHeap;
//             assert rv.ns !! rv.oHeap;
//             assert rv.vs <= rv.ns + oHeap;

//             assert rv.calidObjects(); 
//         }

//         assert k !in vs; // from reqs
//         assert vs == m.Values by { 
//                   assert calid();
//                   reveal calid();
//                   assert calidObjects();
//                   reveal calidObjects();
//                   assert vs == m.Values;
//                    }
//         assert k !in m.Values;


//         reveal rv.calidOK();
//         assert rv.calidOK() by {
//             assert COK(rv.o, rv.oHeap);
//             assert CallOK(rv.oHeap);
//             CallOKfromCOK(k, oHeap);
//             assert CallOK(ks, oHeap);
//             CallOKtoSubset(ks, oHeap);
//             CallOKWiderFocus(ks, {k}, oHeap);
//             assert CallOK(rv.ks, rv.oHeap);
//             CallOKWiderContext({k}, oHeap, ns);
//             CallOKtoSubset(vs, oHeap+ns);
//             CallOKWiderFocus(vs, {k}, oHeap+ns);
//             assert CallOK(rv.vs, rv.oHeap+ns);
//             assert CallOK(rv.ns, rv.oHeap+ns);
//             reveal rv.calidOK(); assert rv.calidOK();
//           }


//         reveal rv.calidMap();
//         assert rv.calidMap() by {
//             reveal rv.calidMap();
//             assert MapOK(rv.m) by {
//                 assert MapOK(m);
//                 assert COK(k, oHeap);
//                 reveal COK();
//                 assert rv.ks == ks + {k};          
//                 assert rv.m.Keys == m.Keys + {k};

//                 reveal rv.calidObjects();
//                 assert rv.calidObjects();
//                 reveal calidObjects();
//                 assert calidObjects();

//                 assert rv.m.Keys == rv.ks;
//                 assert k.AMFO <= ks;

//                 assert forall x <- m.Keys :: x.AMFO <= ks by { 
//                   assert forall x <- m.Keys, oo <- x.AMFO :: oo in m.Keys;
//                 }  
//                 assert k.AMFO <= ks;
//                 assert forall x <- m.Keys+{k} :: x.AMFO <= ks;
//                 assert forall x <- m.Keys+{k} :: x.AMFO <= ks+{k};
//                 assert (ks+{k}) == m.Keys+{k} == rv.ks == rv.m.Keys;
//                 assert forall x <- rv.m.Keys :: x.AMFO <= rv.m.Keys;
//                 assert forall x <- rv.m.Keys, oo <- x.AMFO :: oo in rv.m.Keys;

//                 assert (forall x <- rv.m.Keys :: x.region.Heap? == rv.m[x].region.Heap?);
//                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in x.AMFO);
//                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: x.region.owner in rv.m.Keys);
//                 assert (forall x <- rv.m.Keys |  x.region.Heap? :: rv.m[x.region.owner] == rv.m[x].region.owner );
//             }  //MAapOK

//             assert (forall x <- rv.m.Keys :: (not(inside(x,rv.o)) ==> (rv.m[x] == x))) by 
//             {
//                   reveal rv.calidObjects();
//                   assert ks == m.Keys;
//                   assert rv.ks == rv.m.Keys;
//                   assert (forall x <- ks  :: (not(inside(x,o)) ==> (m[x] == x)));
//                   assert (forall x <- ks  :: (not(inside(x,o)) ==> (rv.m[x] == x)));
//                   assert rv.m[k] == k;
//                   assert (forall x <- {k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
//                   assert (forall x <- ks+{k} :: (not(inside(x,o)) ==> (rv.m[x] == x)));
//                   assert rv.ks == ks+{k};
//                   assert (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
//             }
//             reveal rv.calidObjects();
//             assert ks == m.Keys;
//             assert rv.ks == rv.m.Keys;
//             assert (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
//             assert (forall x <- rv.m.Keys, oo <- x.AMFO :: rv.m[oo] in rv.m[x].AMFO);
//             assert (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO);
//             reveal rv.calidMap();
//             assert rv.calidMap();
//         }
//         reveal rv.calidSheep();
//             reveal rv.calidObjects();
//             assert ks == m.Keys;
//             assert rv.ks == rv.m.Keys;
//         assert not(inside(k, o));
//         reveal calidMap();
//         assert calidMap();
//         reveal calidSheep();
//         assert calidSheep();

//       assert forall x <- ks :: AreWeNotMen(x, this);

//       // assert (forall x <- ks :: 
//       //     if (inside(x,o))
//       //       then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
//       //       else (m[x] == x));

//       //  assert (forall x <- ks        ::  not(inside(x,o)) ==> (m[x] == x));

//       //  assert (forall x <- m.Keys    ::  not(inside(x, o)) ==> (m[x] == x)) by {
//       //     assert NUKE: (forall x <- ks        ::  not(inside(x,o)) ==> (m[x] == x));
//       //     assert (forall x <- m.Keys    ::  not(inside(x, o)) ==> (m[x] == x)) by 
//       //        { 
//       //     reveal calidObjects();
//       //     assert ks == m.Keys;
//       //     reveal NUKE;
//       //     assert (forall x <- ks        ::  not(inside(x,o)) ==> (m[x] == x));
//       //     assert (forall x <- m.Keys    ::  not(inside(x,o)) ==> (m[x] == x));
//       //        }
//       //  }
//       //  assert not(inside(k,o));
//       //  assert (forall x <- {k}       ::  not(inside(x, rv.o)) ==> (rv.m[x] == x)); 
//       //  assert (forall x <- rv.m.Keys ::  not(inside(x, rv.o)) ==> (rv.m[x] == x));

//       //  assert (forall x <- rv.m.Keys :: 
//       //     not(inside(x, rv.o)) ==> (rv.m[x] == x));
//       //  assert (forall x <- rv.m.Keys :: 
//       //     inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));


//   // assert (forall x <- rv.m.Keys | x in m.Keys :: 
//   //         inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))));


// assert rv.ks == rv.m.Keys == (ks+{k});
//       //  assert (forall x <- ks  :: inside(x, rv.o) ==> ((m[x] in rv.ns) && (UniqueMapEntry(m,x))));
//       //  assert (forall x <- {k} :: inside(x, rv.o) ==> ((m[x] in rv.ns) && (UniqueMapEntry(m,x))));



//       //  assert (forall x <- ks  :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))));
//       //  assert (forall x <- {k} :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))));




//       //  assert rv.m.Keys == ks + {k};
//       //  assert rv.m == m[k:=k];
//       //  assert (forall x <- ks+{k}    :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));
//       //  assert (forall x <- rv.m.Keys :: inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));
//       //  assert (forall x <- rv.m.Keys :: not(inside(x, rv.o)) ==> (rv.m[x] == x));

//       //  assert (forall x <- rv.m.Keys :: 
//       //    && (inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))))
//       //    && (not(inside(x, rv.o)) ==> (rv.m[x] == x)));
      
//       //  assert (forall x <- rv.m.Keys :: 
//       //   (&& (inside(x, rv.o) ==> ((rv.m[x] !in rv.ns) && (UniqueMapEntry(m,x))))
//       //    && (not(inside(x, rv.o)) ==> (rv.m[x] == x)))
//       //   ==>
//       //   (if (inside(x,rv.o))
//       //       then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//       //       else (rv.m[x] == x))
//     //    //  );

//     //    forall x <- rv.m.Keys ensures (
//     //       if (inside(x,rv.o))
//     //         then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//     //         else (rv.m[x] == x))
//     //   } { 
//     //     assert (inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(m,x))));
//     //     assert (not(inside(x, rv.o)) ==> (rv.m[x] == x));

//     //     assert if (inside(x,rv.o))
//     //         then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//     //         else true;

//     //     assert if (not(inside(x,rv.o)))
//     //         then (rv.m[x] == x)
//     //         else true;

//     // assert if (inside(x,rv.o))
//     //         then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//     //         else (rv.m[x] == x);


//     //    }

//         assert calidSheep();
//         reveal rv.calidSheep();
//         //reveal UniqueMapEntry();

//         assert ks == m.Keys;
//         // assert (forall x <- ks |    (inside(x,o)) :: (m[x] in ns));
//         // assert (forall x <- ks |    (inside(x,o)) :: (UniqueMapEntry(m,x)));
//         // assert (forall x <- ks | not(inside(x,o)) :: (m[x] == x));
// // 
//         // assert not(inside(k,o));
//         // assert rv.m == m[k:=k];
//         // assert rv.m[k] == k;
//         // assert rv.o == o;
// // 
//         // assert (forall x <- {k} |    (inside(x,rv.o)) :: (rv.m[x] in rv.ns));
//         // assert (forall x <- {k} |    (inside(x,rv.o)) :: (UniqueMapEntry(rv.m,x)));
//         // assert (forall x <- {k} | not(inside(x,rv.o)) :: (rv.m[x] == x));
// // 
//         // assert rv.ks == rv.m.Keys == ks+{k};
//         // assert (forall x <- rv.m.Keys | (inside(x,rv.o)) :: (rv.m[x] in rv.ns));
//         // assert (forall x <- rv.m.Keys :: 
//           // if (x == k) then (not(inside(x,rv.o))) 
//             //  else ((x in m.Keys) && (rv.m[x] == m[x]) && 
//                   // (inside(x,rv.o) ==> (UniqueMapEntry(rv.m,x))))); 
        
// //        assert (forall x <- rv.m.Keys | not(inside(x,rv.o)) :: (rv.m[x] == x));

// reveal AreWeNotMen();  
// reveal UniqueMapEntry();
//         assert forall x <- ks  :: AreWeNotMen(x, this);
//         assert forall x <- {k} :: AreWeNotMen(x, rv);
//         assert forall x <- rv.m.Keys :: AreWeNotMen(x, rv);
        


//         assert rv.calidSheep();

//         reveal rv.calid(); assert rv.calid();
//         rv
//    }






//     opaque function fuckt() : (rv : Map)
//       // fuckt
//       reads oHeap`fields, oHeap`fieldModes
//       reads ns`fields, ns`fieldModes      
//       requires this.valid()
//       ensures rv == this
//       ensures rv.valid()
//       {
// reveal valid();  

//   assert ks == m.Keys;
//   assert vs == m.Values;
//   assert o in oHeap;
//   assert ks <= oHeap;
//   assert ns !! oHeap;
//   assert vs <= ns + oHeap;
//   assert AOK(o, oHeap);
//   assert AllOK(oHeap);
//   assert AllOK(ks, oHeap);
//   assert AllOK(vs, oHeap+ns);
//   assert AllOK(ns, oHeap+ns);
//   assert MapOK(m); // potentiall should expand this out?;
//   assert (forall x <- ks :: (not(inside(x,o)) ==> (m[x] == x)));
//   assert (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO);
//   assert (forall x <- ks ::
//      if (inside(x,o))
//        then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
//        else (m[x] == x));

//         this
//       }


      
//     opaque predicate  {:onlyWANK} valid()
//     //needs to b e inside Map 
//     reads oHeap`fields, oHeap`fieldModes
//     reads ns`fields, ns`fieldModes
//     // are we valid, my preciouw?
//     /// { MOK(this) }  //FUK DAT
//       {
//         && ks == m.Keys
//         && vs == m.Values
//         && o in oHeap
//         && ks <= oHeap
//         && ns !! oHeap
//         && vs <= ns + oHeap
// 
//         && AOK(o, oHeap)
//         && AllOK(oHeap)
//         && AllOK(ks, oHeap)
//         && AllOK(vs, oHeap+ns)
//         && AllOK(ns, oHeap+ns)
// 
//         && MapOK(m) // potentiall should expand this out?
//         && (forall x <- ks :: (not(inside(x,o)) ==> (m[x] == x)))
//         && (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO)
// 
//         && (forall x <- ks :: 
//           if (inside(x,o))
//             then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
//             else (m[x] == x))
//       }
     

//     opaque predicate  {:onlyNUKE} calidORIG()
//     //needs to be inside Map
//     reads oHeap`fields, oHeap`fieldModes
//     reads ns`fields, ns`fieldModes
//     // are we valid, my preciouw?
//     /// { MOK(this) }  //FUK DAT
//       {
//         && ks == m.Keys
//         && vs == m.Values
//         && o in oHeap
//         && ks <= oHeap
//         && ns !! oHeap
//         && vs <= ns + oHeap
// 
//         && COK(o, oHeap)
//         && CallOK(oHeap)
//         && CallOK(ks, oHeap)
//         && CallOK(vs, oHeap+ns)
//         && CallOK(ns, oHeap+ns)
// 
//         && MapOK(m) // potentiall should expand this out?
//         && (forall x <- ks :: (not(inside(x,o)) ==> (m[x] == x)))
//         && (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO)
// 
//         && (forall x <- ks :: AreWeNotMen(x, this))
// 
//         && (forall x <- ks :: x.fieldModes == m[x].fieldModes)
// 
//         // && (forall x <- ks :: 
//         //   if (inside(x,o))
//         //     then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
//         //     else (m[x] == x))
//       }
          



   
// lemma {:onlyAndTheRest} calidMapAndLessFromTheRest( less : set<Object>, more : set<Object> )
//   requires calidObjects() && calidOK()
//   requires less <= more
//   requires calidMapAndTheRest(more)
//   ensures  calidMapAndTheRest(less)
//   {
//     reveal calidMapAndTheRest();
//     assert calidMapAndTheRest(more);
//     assert MapOKAndTheRest(m,more);
//     assert MapOKAndTheRest(m,less);
//     assert calidMapAndTheRest(less);
//   }

//     opaque predicate  {:onlyAndTheRest} calidMapAndTheRest(rest : set<Object>)
//       reads oHeap`fields, oHeap`fieldModes
//       reads ns`fields, ns`fieldModes
//       requires calidObjects() && calidOK()
//        {
//         reveal calidObjects(); assert calidObjects();
//         reveal calidOK(); assert calidOK();
//         && MapOKAndTheRest(m,rest) // potentiall should expand this out?
//         && (forall x <- ks :: (not(inside(x,o)) ==> (m[x] == x)))
//         && (forall x <- ks, oo <- x.AMFO :: 
//                 || (oo in rest)
//                 || (m[oo] in m[x].AMFO))
//        }




// lemma  {:onlyNUKE} ALLISFUCKED() 
//       // reads oHeap`fields, oHeap`fieldModes 
//       // reads ns`fields, ns`fieldModes
//       requires calidObjects() && calidOK() && calidMap()
// {
//   assert calidObjects();
//   assert calidOK();
//   assert calidMap();

/// CCalidSheep() seems BROKEN 

  // assert calidSheep() ==> calidSheep2();
  // assert calidSheep() <== calidSheep2();
  
  // assert calidSheep() ==> calidSheep3();
  // // assert calidSheep() <== calidSheep3();

  // assert calidSheep2() ==> calidSheep3();
  // assert calidSheep2() <== calidSheep3();


// }
      
// 
// 
// 
//     opaque predicate {:onlyNUKE} calidSheep3()
//       reads oHeap`fields, oHeap`fieldModes 
//       reads ns`fields, ns`fieldModes
//       requires calidObjects() && calidOK() && calidMap()
//        {
//         reveal calidObjects(); assert calidObjects();
//         reveal calidOK(); assert calidOK();
//         reveal calidMap(); assert calidMap();
//         assert ks == m.Keys;
//       
//         && (forall x <- ks |    (inside(x,o)) :: (m[x] in ns))
//         && (forall x <- ks |    (inside(x,o)) :: (UniqueMapEntry(m,x)))
//         && (forall x <- ks | not(inside(x,o)) :: (m[x] == x))
//         && (forall x <- ks :: x.fieldModes == m[x].fieldModes)        
//        }
//        
//       

// 
// 
// lemma {:onlyNUKE} sheep12() 
//   requires calidObjects() && calidOK() && calidMap()
//   requires calidSheep2()
//   ensures  calidSheep()
//   {
//         reveal calidObjects(); assert calidObjects();
//         reveal calidOK(); assert calidOK();
//         reveal calidMap(); assert calidMap();
//         reveal calidSheep(), calidSheep2();
// 
//         assert forall x <- ks :: 
//           if (inside(x,o))
//             then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
//             else  (m[x] == x);
// 
//         reveal AreWeNotMen();
//         assert forall x <- ks :: AreWeNotMen(x, this);
// 
//         assert forall x <- ks :: x.fieldModes == m[x].fieldModes;
// 
// 
//         // assert && (forall x <- ks |    (inside(x,o)) :: (m[x] in ns))
//         //        && (forall x <- ks |    (inside(x,o)) :: (UniqueMapEntry(m,x)))
//         //        && (forall x <- ks | not(inside(x,o)) :: (m[x] == x));
//   }

// lemma {:onlyNUKE} sheep21() 
//   requires calidObjects() && calidOK() && calidMap()
//   requires calidSheep()
//   ensures  calidSheep2()
//   {
//         reveal calidObjects(); assert calidObjects();
//         reveal calidOK(); assert calidOK();
//         reveal calidMap(); assert calidMap();
//         reveal calidSheep(), calidSheep2();

//         reveal AreWeNotMen();
//         reveal UniqueMapEntry();

//         assert calidSheep();
//         reveal calidSheep();

//         assert forall x <- ks :: AreWeNotMen(x, this);

//         // assert && (forall x <- ks |    (inside(x,o)) :: (m[x] in ns))
//         //        && (forall x <- ks |    (inside(x,o)) :: (UniqueMapEntry(m,x)))
//         //        && (forall x <- ks | not(inside(x,o)) :: (m[x] == x));

//         assert forall x <- ks :: 
//           reveal AreWeNotMen();
//           reveal UniqueMapEntry();
//           assert AreWeNotMen(x, this);
//           if (inside(x,o))
//             then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
//             else  (m[x] == x);
//   }




// 
// 
// lemma {:onlyNUKE} calidIsORIG()
//   requires calid()
//   ensures  calidORIG()
//   {
//     reveal calid(), calidORIG();
//     assert calid();
// 
//     reveal calidObjects(); assert calidObjects();
//     reveal calidOK(); assert calidOK();
//     reveal calidMap(); assert calidMap();
//     reveal calidSheep(); assert calidSheep();
// 
//     assert calidORIG();
//   }
// 
// 
// lemma {:onlyNUKE} ORIGisCalid()
//   requires calidORIG()
//   ensures  calid()
//   {
//     reveal calid(), calidORIG();
//     assert calidORIG();
// 
// 
//     reveal calidObjects(); assert calidObjects();
//     reveal calidOK(); assert calidOK();
//     reveal calidMap(); assert calidMap();
//     reveal calidSheep(); assert calidSheep();
// 
//     assert calid();
//   }
// 




// lemma {:onlyNUKE} whanmo(rv : Map)
//   requires calid()
// //  requires rv.calid()
// requires rv.calidObjects()
// requires rv.calidOK()
// requires rv.calidMap()
//   requires (forall x <- rv.m.Keys :: 
//         not(inside(x, rv.o)) ==> (rv.m[x] == x))


//   requires forall x <- m.Keys :: x in rv.m.Keys


//   ensures  (forall x <- rv.m.Keys :: 
//           if (inside(x,rv.o))
//             then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//             else (rv.m[x] == x))
//   {
//     reveal calid();  assert calid(); //assert rv.calid();
//     reveal calidObjects(); assert calidObjects(); assert rv.calidObjects();
//     reveal calidOK(); assert calidOK(); assert rv.calidOK();
//     reveal calidMap(); assert calidMap(); assert rv.calidMap();
//     reveal calidSheep(); assert calidSheep();

//     assert && (forall x <- ks |    (inside(x,o)) :: (m[x] in ns))
//              && (forall x <- ks |    (inside(x,o)) :: (UniqueMapEntry(m,x)))
//              && (forall x <- ks | not(inside(x,o)) :: (m[x] == x));


// //  forall x <- m.Keys 
// //    ensures ( if (inside(x,o))
// //             then ((m[x] in rv.ns) && (UniqueMapEntry(m,x))) 
// //             else (m[x] == x) )

//  forall x <- rv.m.Keys 
//    ensures ( if (inside(x,rv.o))
//             then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//             else (rv.m[x] == x) )
//    {
//       //  assert (forall x <- rv.m.Keys :: 
//       //     inside(x, rv.o) ==> ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))));

// //     assert inside(x, rv.o) ==> (UniqueMapEntry(rv.m,x));

//       if (inside(x,rv.o)) {
//           assert (inside(x,rv.o));
//           assert inside(x, rv.o) ==> ((rv.m[x] in rv.ns));
//           assert ((rv.m[x] in rv.ns));
//           assert (UniqueMapEntry(rv.m,x));
//       } else {
//           assert not(inside(x,rv.o));
//           assert (rv.m[x] == x);
//       }
//    }
// }






predicate {:onleee}  MOK(m : Map) 
//is this Clone MAP OK?
//sort of like therapy but for Clonemaps
//see Clone_MAP)_OK for moredetails ...
 reads m.oHeap`fields, m.oHeap`fieldModes
 reads m.ns`fields, m.ns`fieldModes
{ pClone_MAP_OK( m.m, m.ks, m.vs, m.o, m.oHeap, m.ns) }


// method {:onleee} mfuckee(rv : Map)
//   requires rv.valid()


// {
//   //reveal rv.valid();

//   assert rv.ks == rv.m.Keys;
//   assert rv.vs == rv.m.Values;
//   assert rv.o in rv.oHeap;
//   assert rv.ks <= rv.oHeap;
//   assert rv.ns !! rv.oHeap;
//   assert rv.vs <= rv.ns + rv.oHeap;
//   assert AOK(rv.o, rv.oHeap);
//   assert AllOK(rv.oHeap);
//   assert AllOK(rv.ks, rv.oHeap);
//   assert AllOK(rv.vs, rv.oHeap+rv.ns);
//   assert AllOK(rv.ns, rv.oHeap+rv.ns);
//   assert MapOK(rv.m);
//   assert (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
//   assert (forall x <- rv.ks, oo <- x.AMFO:: rv.m[oo] in rv.m[x].AMFO);
//   assert (forall x <- rv.ks ::
//      if (inside(x,rv.o))
//        then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//        else (rv.m[x] == x));

// }


predicate pClone_MAP_OK(m : Mapping, ks : set<Object>, vs : set<Object>, o : Object, oHeap : set<Object>, ns : set<Object>)
//is a clone map OK
//m : Mapping 
//ks - set, keys of the mapping   (must be m.Keys, subset of oHeap)
//vs - set, values or the mapping (must be m.Values, subset of oHeap + ns)
//o - Owner within which the clone is being performaed, in oHeap
//oHeap - original (sub)heap contianing the object being cloned and all owners and parts 
//ns - new objects  (must be !! oHeap,   vs == oHeap + ns 
 reads oHeap`fields, oHeap`fieldModes
 reads ns`fields, ns`fieldModes
{
  && ks == m.Keys
  && vs == m.Values
  && o in oHeap
  && ks <= oHeap
  && ns !! oHeap
  && vs <= ns + oHeap

  && AOK(o, oHeap)
  && AllOK(oHeap)
  && AllOK(ks, oHeap)
  && AllOK(vs, oHeap+ns)
  && AllOK(ns, oHeap+ns)

  && MapOK(m) // potentiall should expand this out?
  && (forall x <- ks :: (not(inside(x,o)) ==> (m[x] == x)))
  && (forall x <- ks, oo <- x.AMFO :: m[oo] in m[x].AMFO)

  && (forall x <- ks :: 
     if (inside(x,o))
       then ((m[x] in ns) && (UniqueMapEntry(m,x))) 
       else (m[x] == x))
}


// method {:onleee} walkiesClean(a : Object, o : Object, m' : Mapping, os' : set<Object>, oHeap : set<Object>) 
//       returns (b : Object, m : Mapping, os : set<Object>)
// //  decreases (oHeap - m'.Keys)

//   need to be incode Map or something... 
// 
//
//
// //abandoned version
//     opaque function {:verify false} extPutOut(m : Map, k : Object) : (r : Map)
//       //put k -> k into map
//       reads m.oHeap`fields, m.oHeap`fieldModes, k
//       reads m.ns`fields, m.ns`fieldModes, m.vs`fields, m.vs`fieldModes
//       requires m.valid()
//       requires k !in m.ks
//       requires k in m.oHeap
//       requires k !in m.vs
//       requires not(inside(k, m.o))
//       
//       requires VOK: AllOK(m.vs, m.vs+m.oHeap) 
//       ///grr.. just stand up & stand by...
// 
//       ensures  r == Map(m.m[k:=k], m.ks+{k}, m.vs+{k}, m.o, m.oHeap, m.ns)
//       ensures  r.valid()
//       { 
//         reveal m.valid();
//         var rv : Map := Map(m.m[k:=k], m.ks+{k}, m.vs+{k}, m.o, m.oHeap, m.ns);
//         reveal rv.valid();
// 
// //comment delete
// //can turn off ensuresvaued
// ///can turn off asert valid at bottom of method
// // commoent out mostof thse 
// // turn on one at a time?
// 
// 
//               assert rv.ks == rv.m.Keys;
//               assert rv.vs == rv.m.Values;
//               assert rv.o in rv.oHeap;
//               assert rv.ks <= rv.oHeap;
//               assert rv.ns !! rv.oHeap;
//               assert rv.vs <= rv.ns + rv.oHeap;
//               assert AOK(rv.o, rv.oHeap);
//               assert AllOK(rv.oHeap);
//               assert AllOK(rv.ks, rv.oHeap);
//               assert AllOK(rv.vs, rv.oHeap+rv.ns);
//               assert AllOK(rv.ns, rv.oHeap+rv.ns);
//               assert MapOK(rv.m) by {
//                 assert MapOK(m.m);
//                 assert rv.m == m.m[k:=k];
//               //  assert rv.m == MappingPlusOneKeyValue(m.m,k,k);
//                 assert AllOK(m.vs, m.vs+m.oHeap)  by { reveal VOK; }
//                 assert rv.m == F_DAF(m.m,k,k,m.oHeap);
//                 assert MapOK(rv.m);
//               }
//               assert (forall x <- rv.ks :: (not(inside(x,rv.o)) ==> (rv.m[x] == x)));
//               assert (forall x <- rv.ks, oo <- x.AMFO:: rv.m[oo] in rv.m[x].AMFO);
//               assert (forall x <- rv.ks ::
//                 if (inside(x,rv.o))
//                   then ((rv.m[x] in rv.ns) && (UniqueMapEntry(rv.m,x))) 
//                   else (rv.m[x] == x));
// 
// 
//         assert rv.valid();
//         rv
//        }
// 
// 
// 
// 
// 
// 













lemma  AintNoValues<K,V>(v : V, m : map<K,V>)
{
}











//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 

method {:verify false}  Orig_Clone_Via_Map(a : Object, m' : Map)
      returns (b : Object, m : Map)
  decreases (m'.oHeap - m'.ks), a.AMFO

  requires m'.calid()
  requires a in m'.oHeap  //technically redundant given COKx
  requires COK(a, m'.oHeap)

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
  ensures  m.o == m'.o
  ensures  m.oHeap == m'.oHeap
  ensures  m.ns >= m'.ns
//  ensures  if (inside(a, m'.o)) then (b in m.ns) else (b == a)
//  ensures  reveal m.calid(); reveal m.calidMap(); assert m.calid(); assert 
  ensures MapOK(m.m) && a.AMFO <= m.ks
{ 
  m := m';
  b := a; 
  print "CALL Clone_Via_Map:", fmtobj(a), " owner:", fmtobj(m.o), "\n";

  assert COKSTART: COK(a, m.oHeap);

  print "Clone_Via_Map started on:", fmtobj(a), "\n";

//hmmm
//   reveal m.calid();
//   assert m.calid();
//   reveal m.calidOK();
//   assert m.calidOK();
//   reveal m.calidObjects();
//   assert m.calidObjects();
//   reveal m.calidMap();
//   assert m.calidMap();
// 
//   assert MapOK(m.m);

  var  mmKeysNA := m.m.Keys;
  
  assert unchanged(mmKeysNA);

  // assert (forall x <- mmKeysNA, oo <- x.AMFO :: oo in m.m.Keys);
  // assert (forall x <- mmKeysNA :: x.region.Heap? == m.m[x].region.Heap?);
  // assert (forall x <- mmKeysNA |  x.region.Heap? :: x.region.owner in x.AMFO);
  // assert (forall x <- mmKeysNA |  x.region.Heap? :: x.region.owner in m.m.Keys);
  // assert (forall x <- mmKeysNA |  x.region.Heap? :: m.m[x.region.owner] == m.m[x].region.owner );
  // assert (forall x <- mmKeysNA, oo <- x.AMFO :: m.m[oo] in m.m[x].AMFO);


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


//MAKE ALL THE ERRORS GO AWAY
  assert  m.calid();
  assert  a in m.ks;
  assert  a in m.m.Keys;
  assert  b in m.vs;
  assert  b in m.m.Values;
  assert  a in m.m.Keys && m.at(a) == b;
  assert  COK(b,m.oHeap+m.ns);
  assert  mapLEQ(m'.m,m.m);
  assert  m.ks >= m'.ks + {a};
  assert  m.vs >= m'.vs + {b};
  assert  m.o == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns >= m'.ns;


 assert  MapOK(m.m) && a.AMFO <= m.ks by
   {
    reveal m.calid();
    assert m.calid();
    reveal m.calidOK();
    assert m.calidOK();
    reveal m.calidObjects();
    assert m.calidObjects();
    reveal m.calidMap();
    assert m.calidMap();

    assert  MapOK(m.m) && a.AMFO <= m.ks;
   }

     assert unchanged(mmKeysNA);

      return;
  } // a in ks, already cloned
  
//MAKE ALL THE ERRORS GO AWAY
  assert  m.calid();
  assert  a in m.ks;
  assert  a in m.m.Keys;
  assert  b in m.vs;
  assert  b in m.m.Values;
  assert  a in m.m.Keys && m.at(a) == b;
  assert  COK(b,m.oHeap+m.ns);
  assert  mapLEQ(m'.m,m.m);
  assert  m.ks >= m'.ks + {a};
  assert  m.vs >= m'.vs + {b};
  assert  m.o == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns >= m'.ns;
  assert  MapOK(m.m) && a.AMFO <= m.ks;





  //   reveal m.calidObjects();
  //   assert m.calidObjects();

  assert ANKS: a !in m.ks;
  
  // assert m.calid();  //join from the if?
  assert COKFOURWAYS: m.calid(); 

  // assert CallOK(m.oHeap) by { reveal m.calidOK(); assert m.calidOK(); }
  // 
  // assert COK(a, m.oHeap);

 //  return;  //Umm what's this doing here???

///redoing outside case
  if (outside(a,m.o)) {
   print "RETN Clone_Via_Map ", fmtobj(a), " is really outside ", fmtobj(m.o), "so maps to itself (share not clone)\n";

          b := a;

  // assert outside(a,m.o);
 
      if (a.region.Heap?) {
        print "Clone_Via_Map outside owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";

        assert a.OwnersValid() by {
        reveal m.calid();
        assert m.calid();
        reveal m.calidOK();
        assert m.calidOK();
        assert CallOK(m.oHeap);
        assert a in m.oHeap;
        COKfromCallOK(a, m.oHeap);
        assert COK(a, m.oHeap);  
        reveal COK();
        assert a.Valid();
        assert a.OwnersValid();
       } 

        // assert a.OwnersValid();
        assert a.AMFO > a.region.owner.AMFO;
        COKfromCallOK(a, m.oHeap);
        assert COK(a, m.oHeap);
        a.CallMyOwnersWillWitherAway(a, m.oHeap);
        assert COK(a.region.owner, m.oHeap); 

//preconditions for the call..
  // assert m.calid();
  // assert a.region.owner in m.oHeap;  
assert COK(a.region.owner, m.oHeap); 
  // assert outside(a.region.owner, m.o); //TEMP TO WRITEOUTSIDE CASE

        var rowner, rm := Clone_Via_Map(a.region.owner, m);

        ///BUT things hop around insidef, e.g. so we've already copied "a" in the recursive call
        ///can we just be done?
        ///Hmm. fuck I hate this shit

      //Hmm do we even need to do this?
      //or won't the recursive call handle it anyway??
        if (a in rm.ks) {
            m := rm;
            b := rm.at(a);

            assert m.calid();
            assert CallOK(m.vs, m.oHeap+m.ns);
            assert b in m.m.Values; 
            assert m.m.Values == m.vs;
            assert b in m.vs;
            COKfromCallOK(b, m.vs, m.oHeap+m.ns);
            assert COK(b, m.oHeap+m.ns);


  //MAKE ALL THE ERRORS GO AWAY
//  arseume  m.calid();
//  arseume  a in m.ks;
//  arseume  a in m.m.Keys;
//  arseume  b in m.vs;
//  arseume  b in m.m.Values;
//  arseume  a in m.m.Keys && m.at(a) == b;
//  arseume  COK(b,m.oHeap+m.ns);
//  arseume  mapLEQ(m'.m,m.m);
//  arseume  m.ks >= m'.ks + {a};
//  arseume  m.vs >= m'.vs + {b};
//  arseume  m.o == m'.o;
//  arseume  m.oHeap == m'.oHeap;
//  arseume  m.ns >= m'.ns;
//  arseume  MapOK(m.m) && a.AMFO <= m.ks;


            return; //should work because Clone_Via_Map meets all the conditiosn, right???
        }

        assert a !in rm.ks;

//    //maintaing MapOK
        assert AMFOOKRM: a.AMFO <= rm.ks by {
            reveal rm.calid();
            assert rm.calid();
            reveal rm.calidMap();
            assert rm.calidMap();
            assert MapOK(rm.m);
            assert (forall x <- rm.ks, oo <- x.AMFO :: oo in rm.ks);
            assert a.AMFO <= rm.ks;
        }     



        assert a in rm.oHeap; 
        assert COK(a, rm.oHeap);
        reveal COK();
        assert a.AMFO <= rm.ks;
        OutsidersArentMapValues(a,rm);
        assert a !in rm.vs;
        assert not(inside(a, rm.o)); 

        //m := rm[a:=b];     
        m := rm.putOutside(a);
        assert m.m == MappingPlusOneKeyValue(rm.m,a,a);
        assert m.calid(); 
        MapOKFromCalid(m);
        assert MapOK(m.m);

        assert MapOK(m.m);
        assert mapLEQ(rm.m, m.m);
        
        assert a.AMFO <= m.ks by
            {
            reveal AMFOOKRM;
            assert a.AMFO <= rm.ks;
            SubsetOfMapLEQKeys(a.AMFO, rm.m, m.m);
            assert a.AMFO <= m.ks;
          }


      //END outside  HEAP OBJECT
    } else {
      //"world"" OBJECT 
        assert COK(a,m.oHeap);
        reveal COK();
        assert a.Ready();
        assert a.region.World?;
        assert a.AMFO == {};
        assert m.calid(); 
        reveal m.calid();
        reveal m.calidSheep();
        assert m.calidSheep();

        print "Clone_Via_Map world:", fmtobj(a),"\n";

        assert CallOK(m.oHeap);

        b := a;

        assert a !in m.ks;
        assert a in m.oHeap;
        assert m.oHeap !! m.ns;
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
        assert (forall x <- m.ks :: x.AMFO <= m.ks); 

        assert a !in m.vs;
        m := m.putOutside(a);   ///HOPEY?  CHANGEY?
  }//end of outside / world 
 
            assert m.calid();
            assert CallOK(m.vs, m.oHeap+m.ns);
            assert b in m.m.Values; 
            assert m.m.Values == m.vs;
            assert b in m.vs;
            COKfromCallOK(b, m.vs, m.oHeap+m.ns);
            assert COK(b, m.oHeap+m.ns);


  //MAKE ALL THE ERRORS GO AWAY
  // assume  m.calid();
  // assume  a in m.ks;
  // assume  a in m.m.Keys;
  // assume  b in m.vs;
  // assume  b in m.m.Values;
  // assume  a in m.m.Keys && m.at(a) == b;
  // assume  COK(b,m.oHeap+m.ns);
  // assume  mapLEQ(m'.m,m.m);
  // assume  m.ks >= m'.ks + {a};
  // assume  m.vs >= m'.vs + {b};
  // assume  m.o == m'.o;
  // assume  m.oHeap == m'.oHeap;
  // assume  m.ns >= m'.ns;
  // assume  MapOK(m.m) && a.AMFO <= m.ks;


  return;  //we may as well just return here.
           //we've done all we need to do.  I think.

 }///END OF THE OUTSIDE CASE
 else 
 { //start of the Inside case 

assert COK(a, m.oHeap);
assert m.calid();
assert inside(a,m.o);
//assert forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.at(x) == x));

  if (a.region.Heap?) {  //start of inside heap case
        print "Clone_Via_Map owners:", fmtobj(a), " owned by ", fmtobj(a.region.owner) ,"\n";

        assert m.calid();
        reveal m.calid();
        assert m.calidOK();
        reveal m.calidOK();      
        COKfromCallOK(a, m.oHeap);
        AOKfromCOK(a, m.oHeap);
        assert COK(m.o, m.oHeap);
        assert CallOK(m.oHeap);
        AllOKfromCallOK(m.oHeap);
        AOKAMFO(a, m.oHeap);
        assert a.region.owner in a.AMFO;
        assert AOK(a.region.owner, m.oHeap);
        COKfromAOK(a.region.owner, m.oHeap);
        assert COK(a.region.owner, m.oHeap);
  
        var rowner, rm := Clone_Via_Map(a.region.owner, m);
 
        assert COK(rowner, rm.oHeap+rm.ns);

        assert COK(a.region.owner, rm.oHeap);
        assert CallOK(rm.oHeap);
        assert CallOK(rm.ks, rm.oHeap);
        assert CallOK(rm.vs, rm.oHeap+rm.ns);
        assert CallOK(rm.ns, rm.oHeap+rm.ns);

assert rm.calid();
assert rm.calidObjects();
assert rm.calidOK();
assert rm.calidMap();
reveal rm.calid();
reveal rm.calidObjects();
reveal rm.calidOK();
reveal rm.calidMap();

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

assert COK(rowner, rm.oHeap+rm.ns);  //ensured by clone

///need this for later...
assert COK(rowner, rm.oHeap+rm.ns);
assert CallOK(rm.oHeap+rm.ns);


        // && COK(rm.oo, oHeap)
        // && CallOK(oHeap)
        // && CallOK(rm.ks, oHeap)
        // && CallOK(rm.vs, oHeap+rm.ns)
        // && CallOK(rm.ns, oHeap+rm.ns)

        ///BUT things hop around insidef, e.g. so we've already copied "a" in the recursive call
        ///can we just be done?
        ///Hmm. fuck I hate this shit

        if (a in rm.ks) {
            m := rm;
            b := rm.at(a);
            assert m.calid();
            assert CallOK(m.vs, m.oHeap+m.ns);
            assert b in m.m.Values; 
            assert m.m.Values == m.vs;
            assert b in m.vs;
            COKfromCallOK(b, m.vs, m.oHeap+m.ns);
            assert COK(b, m.oHeap+m.ns);


  //(MAKE ALL THE ERRORS GO AWAY)
  assert  m.calid();
  assert  a in m.ks;
  assert  a in m.m.Keys;
  assert  b in m.vs;
  assert  b in m.m.Values;
  assert  a in m.m.Keys && m.at(a) == b;
  assert  COK(b,m.oHeap+m.ns);
  assert  mapLEQ(m'.m,m.m);
  assert  m.ks >= m'.ks + {a};
  assert  m.vs >= m'.vs + {b};
  assert  m.o == m'.o;
  assert  m.oHeap == m'.oHeap;
  assert  m.ns >= m'.ns;
  assert  MapOK(m.m) && a.AMFO <= m.ks;




            return; //should work because Clone_Via_Map meets all the conditiosn, right???
        }

assert COK(rowner, rm.oHeap+rm.ns);
assert CallOK(rm.oHeap+rm.ns);

        b := new Object.cake(protoTypes, rowner, rm.oHeap+rm.ns, "clone of " + a.nick);

        assert fresh(b);
        assert b !in rm.oHeap;
        assert b !in rm.m.Values;
        assert a !in rm.m.Keys;
        assert COK(b, (rm.oHeap+rm.ns)+{b});
        // COKWiderContext(b, )
        // assert COK(b, {b} + rm.oHeap+rm.m.Values);
        assert a.region.Heap? == b.region.Heap?;


//call to putInside...

//         //requires v !in (oHeap + ns)  //7108
//                requires v !in vs //7107
// //7104 |       requires COK(v, oHeap+ns+{v})

//    //requires k.AMFO <= ks  

        assert rm.calid();
        assert rm.calidOK();
        assert rm.calidMap();
        reveal rm.calid();
        reveal rm.calidOK();
        reveal rm.calidMap();
        assert COK(a,rm.oHeap);
        reveal COK();
        assert a.AMFO <= rm.oHeap;
        assert a !in rm.ks by { reveal ANKS; }
        assert b !in rm.vs;
        assert COK(b, rm.oHeap+rm.ns+{b});
        assert b !in (rm.oHeap+rm.ns);

                   
        m := rm.putInside(a,b);  
        assert m.m == MappingPlusOneKeyValue(rm.m,a,b);

      //END inside HEAP OBJECT 
    } else {
      //inside "world"" OBJECT

        assert COK(a, m.oHeap) by { reveal COKSTART; }

        assert m.calid(); 
        reveal m.calid();
        reveal m.calidOK();
        assert m.calidOK();

        print "Clone_Via_Map world:", fmtobj(a),"\n";

        assert CallOK(m.oHeap);   
        AllOKfromCallOK(m.oHeap,m.oHeap);

        assert BEFORE: m.calid(); 
    
        b := new Object.frozen2(a.fieldModes, m.oHeap);

        b.nick := "clone of" + a.nick; 

        assert fresh@BEFORE(b);
        assert b !in m.oHeap;
        assert b !in m.ns;
        assert unchanged@BEFORE(m.oHeap`fields, m.oHeap`fieldModes);
        assert unchanged@BEFORE(m.ns`fields, m.ns`fieldModes);

        assert m.calid();

        assert fresh(b);
        assert COK(a, m.oHeap) by { reveal COKSTART; }
        assert COK(b, m.oHeap+{b});
        COKWiderContext(b, m.oHeap+{b}, m.ns);
        assert (m.oHeap+{b})+m.ns == m.oHeap+m.ns+{b};
        assert COK(b, m.oHeap+m.ns+{b});
 
        m := m.putInside(a,b);  
    }   //end of inside world heap case
 } //end of inside case 
 
  assert a.region.Heap? == b.region.Heap?;
  assert b in m.vs;


  assert m.calid();
  assert CALID10K: m.calid();

  assert CallOK(m.vs, m.oHeap+m.ns);
  assert b in m.m.Values; 
  assert m.m.Values == m.vs;
  assert b in m.vs;
  COKfromCallOK(b, m.vs, m.oHeap+m.ns);
  assert COK(b, m.oHeap+m.ns);


  assert m.calid();

print "<<<<<<<<<<<\n";
print "just cloned ", fmtobj(a), " as ", fmtobj(b), "\n";

  assert m.m[a] == b;  //mmmKJX
  // assert (a in m.ks) ==> (m[a] == b);  //mmmKJX


  assert m.calid();

  assert COK(b, m.oHeap+m.ns);
  assert HEREB: COK(b, m.oHeap+m.ns);

// print "<<<<<<<<<<<\n";
// printmapping(m.m);
// print "<<<<<<<<<<<\n";
// 

//   assert m.calid();   assert CALID10K20: m.calid();
// 
//   var ns : seq<string> := set2seq(a.fields.Keys);
//   print "Clone_Via_Map fields:", fmtobj(a), " fields=", fmtseqstr(ns), "\n";  
// 
//   assert old@CALID10K( m.calid() );
//   assert unchanged@CALID10K(m.oHeap`fields, m.oHeap`fieldModes);
//   assert unchanged@CALID10K(m.ns`fields, m.ns`fieldModes);
//   assert CALID10K17: m.calid() by { reveal CALID10K; reveal CALID10K20;  assert old@CALID10K( m.calid() ); }
//   assert mapLEQ(m'.m,m.m);
// 
// 
// 
//   for i := 0 to |ns|
//      invariant AOK(b, m.oHeap+m.ns)
//      invariant mapLEQ(m'.m,m.m)
//      invariant a in m.oHeap
//      invariant m.o in m.oHeap
//      invariant AllOK(m.oHeap, m.oHeap)
//      invariant AllOK(m.vs, m.oHeap + m.ns)
//      invariant  forall x <- m.ks :: (not(inside(x,m.o)) ==> (m.at(x) == x))
//    {
//         var n : string := ns[i];
//         var ofv : Object := a.fields[n];   
//     print "  ",fmtobj(a),".",n," :=", fmtobj(ofv), "\n";
//     print "    (recurse on field ",n,")\n";
// 
// 
//         var rfv, rm := Clone_Via_Map(ofv, m);
// 
//         assert rfv in rm.ns;
// 
//         assert m.m[a.fields[n]] == rfv;
// 
//         assert forall oo <- ofv.AMFO :: rm.at(ofv) in rfv.AMFO;
// 
//         if (rfv.region.Heap?) 
//         {
//           assert AOK(a,m.oHeap);
//           assert a.AllOutgoingReferencesAreOwnership(m.oHeap);
//           assert refOK(a,ofv);  //******************** this is key!!! */
//           assert inside(a,ofv.region.owner);
//           assert || ofv == anm    n
//                  || a in ofv.region.owner.AMFO;
// 
//           assert inside(a,ofv.region.owner);
// 
//           assert inside(b, rfv.region.owner);
//           assert refOK(b, rfv); //******************** this is key!!! */
//         } else {
//           assert rfv.region.World?;
//           assert refOK(b, rfv); //******************** this is key!!! */
//         }
// 
//         assert refOK(b, rfv);
// 
//         label HERE:
// 
//         b.fields := b.fields[n := rfv]; //  MOVED
// 
//         // assert unchanged@HERE( oHeap - {b} );
//         // assert AllOK(oHeap - {b}, oHeap );
// 
//         assert refOK(b, rfv);
// 
//        m  := rm;
// 
// 
//   assert os  == oHeap - m.ks;
// 
//         assert b.Valid() && b.TRUMP();
// 
//   assert AllOK(oHeap, oHeap);
//   assert AOK(b, oHeap + m.vs);
//   assert AllOK(m.vs, oHeap + m.vs);
//   assert forall x <- m.ks :: (not(inside(x,o)) ==> (m[x] == x));
//   assert m.ks <= (m'.ks + os');
//   assert m.ks !! os;
//   assert mapLEQ(m',m);
//   assert m[a] == b;  //mmmKJX
//   assert (a in m.ks) ==> (m[a] == b);  //mmmKJX
// 
//   }
//      print "RETN Clone_Via_Map done ", fmtobj(a), "\n";
// 
//   assert COK(b, m.oHeap+m.ns) by { reveal HEREB; }
//   assert mapLEQ(m'.m,m.m);
// 
// reveal m.calid();
// assert m.calid() by { reveal CALID10K17; }
// 
//   assert m.m[a] == b;
// 
//   assert m.at(a) == b;  //mmmKJX
//   assert a in m.ks;   //mmmKJX
//   assert b in m.ns; //mmmKJX
// 
//   assert COK(b, m.oHeap+m.ns);
// 
//     assert mapLEQ(m'.m,m.m);
//  
//   
//     assert CallOK(m.oHeap);
//     assert COK(a, m.oHeap);
//     assert COK(b, m.oHeap + m.ns);
//     assert CallOK(m.vs, m.oHeap+m.ns);
//     assert COK(b, m.oHeap  + m.ns);
// 
//  
//     reveal m.calidObjects(); assert m.calidObjects();
// 
// 
//         assert COK(m.o, m.oHeap);
//         assert CallOK(m.oHeap);
//         assert CallOK(m.ks, m.oHeap);
//         assert CallOK(m.vs, m.oHeap+m.ns);
//         assert CallOK(m.ns, m.oHeap+m.ns);
// 
//     reveal m.calidOK(); assert m.calidOK();
// 
//    mmKeysNA := m.oHeap;
// 
// assert unchanged(mmKeysNA);
// 
//   assert (forall x <- mmKeysNA, oo <- x.AMFO :: oo in m.m.Keys);
//   assert (forall x <- mmKeysNA :: x.region.Heap? == m.m[x].region.Heap?);
//   assert (forall x <- mmKeysNA |  x.region.Heap? :: x.region.owner in x.AMFO);
//   assert (forall x <- mmKeysNA |  x.region.Heap? :: x.region.owner in m.m.Keys);
//   assert (forall x <- mmKeysNA |  x.region.Heap? :: m.m[x.region.owner] == m.m[x].region.owner );
//   assert (forall x <- mmKeysNA, oo <- x.AMFO :: m.m[oo] in m.m[x].AMFO);
//     
// mmKeysNA := m.ns;
// 
// {
//         assert (forall x <- mmKeysNA, oo <- x.AMFO :: oo in m.m.Keys);
//         assert (forall x <- mmKeysNA :: x.region.Heap? == m.m[x].region.Heap?);
//         assert (forall x <- mmKeysNA |  x.region.Heap? :: x.region.owner in x.AMFO);
//         assert (forall x <- mmKeysNA |  x.region.Heap? :: x.region.owner in m.m.Keys);
//         assert (forall x <- mmKeysNA |  x.region.Heap? :: m.m[x.region.owner] == m.m[x].region.owner );
//         assert (forall x <- mmKeysNA, oo <- x.AMFO :: m.m[oo] in m.m[x].AMFO);
// }        
// 
// 
// 



        assert MapOK(m.m); // potentiall should expand this out?

        assert (forall x <- mmKeysNA :: (not(inside(x,m.o)) ==> (m.m[x] == x)));
        assert (forall x <- mmKeysNA, oo <- x.AMFO :: m.m[oo] in m.m[x].AMFO);
    

    
    reveal m.calidMap(); assert m.calidMap();
    reveal m.calidObjects(); assert m.calidObjects();
    reveal m.calidOK(); assert m.calidOK();
    assert m.ks == m.m.Keys;

    reveal m.AreWeNotMen(); 
    assert forall x <- m.m.Keys :: m.AreWeNotMen(x, m);

    reveal m.calidSheep(); assert m.calidSheep();

    reveal m.calid(); assert m.calid();

    assert MapOK(m.m) && a.AMFO <= m.ks;
  
// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
//MAKE ALL THE ERRORS GO AWAY!

//  arseume  m.calid();
//  arseume  a in m.ks;
//  arseume  a in m.m.Keys;
//  arseume  b in m.vs;
//  arseume  b in m.m.Values;
//  arseume  a in m.m.Keys && m.at(a) == b;
//  arseume  COK(b,m.oHeap+m.ns);
//  arseume  mapLEQ(m'.m,m.m);
//  arseume  m.ks >= m'.ks + {a};
//  arseume  m.vs >= m'.vs + {b};
//  arseume  m.o == m'.o;
//  arseume  m.oHeap == m'.oHeap;
//  arseume  m.ns >= m'.ns;
//  arseume  MapOK(m.m) && a.AMFO <= m.ks;


    return;
}//end Orig_Clone_Via_Map

// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 

// 
// lemma  KeysValuesFromCalid(m : Map, k : Object, v : Object)
//   requires m.calid()
//   ensures  (k in m.m.Keys)   == (k in m.ks)
//   ensures  (v in m.m.Values) == (v in m.vs)
// { 
//    reveal m.calid();
//    assert m.valid();
//    reveal m.calidObjects();
//    assert m.calidObjects();
// } 



//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 

////////////////////////////////////////////////////////////////



// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 
// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// 




////////////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////////////////////////////




//////////////////////////////////////////////////////////////////////////
/// or a set of objecgs * a set of fields (= object, string pairs)
  
datatype Yall = Yall(o : Object, n : string) | Yobject(o : Object)



  function yall(os: set<Object>) : set<Yall>
  reads os`fields
  {
set o <- os,  n <- o.fields :: Yall(o,n)
  }

  