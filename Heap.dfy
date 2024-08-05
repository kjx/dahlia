/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
// clasls Memory.  NUFF SAID - mostly opcodes
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

class Memory
{
  ///rather truncated!
  //probaby these shouldn't be in here

  //do I want an "objects" "state" "heap" here?
  //what sh9iould it be calledw?
  //Object Graph, right?  with a horrible name
  var CurrentObjectGraph : set<Object> //rename too "heap"

  constructor()
    ensures Valid()
  {
    CurrentObjectGraph := {};
    new;
    //////reveal Valid();
  }
  



//should I just assert Valid2()??  why or why not
//ans: baceuse some state is valid != some state is the same as the initiakl state
twostate predicate {:done} UnchangedFUCK()
   reads set o1 <- CurrentObjectGraph, o2 <-     o1.ValidReadSet() :: o2
  // reads set o1 <- CurrentObjectGraph, o2 <- old(o1.ValidReadSet()) :: o2
   reads `CurrentObjectGraph, CurrentObjectGraph`fields
   reads CurrentObjectGraph
{
    && (forall o <- CurrentObjectGraph :: old(allocated(o)) ==> (old(o.fields)) == o.fields)
    && (old(CurrentObjectGraph) == CurrentObjectGraph)
    && (forall o <- old(CurrentObjectGraph) :: o in CurrentObjectGraph)
    // && ((set o1 <- old(CurrentObjectGraph), o2 <-  old(o1.ValidReadSet()) :: o2) == 
    //     (set o1 <-     CurrentObjectGraph, o2 <-       o1.ValidReadSet() :: o2)
    // )
   // && (forall o <- CurrentObjectGraph :: (old(allocated(o)) && allocated(o))==> (unchanged(o)))
    && (forall o1 <- CurrentObjectGraph, o2 <- o1.ValidReadSet() :: old(allocated(o2)) ==> unchanged(o2))
    && (unchanged(`CurrentObjectGraph))
      && (unchanged(CurrentObjectGraph`fields))
    && Valid()
    
}

  // do I want a aValid() here?  
/*opaque*/ predicate {:timeLimit 10}  Valid() //Memory.Valid()
    reads CurrentObjectGraph
    reads (set o1 <- CurrentObjectGraph, o2 <- o1.ValidReadSet() :: o2)
    reads `CurrentObjectGraph
    reads CurrentObjectGraph`fields
  {
    ////////reveal Object.Ready();
    && (forall o <- CurrentObjectGraph :: o.Ready() && o.Valid())
    && StandaloneObjectsAreValid(CurrentObjectGraph)
    && OutgoingReferencesAreInTheseObjects(CurrentObjectGraph) 
    && IncomingReferencesConstraintsOK(edges(CurrentObjectGraph)) 
  }

  twostate predicate Valid2()  
    reads CurrentObjectGraph
    reads (set o1 <- CurrentObjectGraph, o2 <- o1.ValidReadSet() :: o2)
    reads `CurrentObjectGraph
    reads CurrentObjectGraph`fields
    { Valid()}



/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
  method {:timeLimit 120} nul(o : Object, f : string)
    requires Valid()

    requires o in CurrentObjectGraph
    requires f in o.fieldModes
    requires f in o.fields
    requires o.fieldModes[f].Owned?  //that's a bit overkil isn't it?
    requires o.Valid()

    // //commented out earlier//    requires o.fieldModes[f].Owned? ==> (|(set e <- edges(CurrentObjectGraph) :: e.t == (o.fields[f]))| == 1)

    // ensures  o.fields.Keys == old(o.fields.Keys) - {f}
    // ensures  o.fields == old(RemoveKey(o.fields,f)) 
    // ensures  forall e <- edges(CurrentObjectGraph) :: not( e.f == o && e.n == f )
    // ensures  forall e <- edges(CurrentObjectGraph) :: not( e.f == o && e.n == f && e.t == old(o.fields[f]) )
    // ensures  o.fieldModes[f].Owned? ==> (forall e <- edges(CurrentObjectGraph) :: not( e.t == old(o.fields[f]) ))
    // ensures  o.fieldModes[f].Owned? ==> (refCountEdges(old(o.fields[f]), edges(CurrentObjectGraph)) == 0)

    // ensures o.Ready() && o.Valid()
    // ensures Valid()

    // ensures  unchanged(this`CurrentObjectGraph)
    // //ensures  forall x <- CurrentObjectGraph :: (x != o) ==> (x.fields == old(x.fields))
    // ensures  forall x <- CurrentObjectGraph :: (x != o) ==> (unchanged(x`fields))

    // ensures edges(CurrentObjectGraph) == old(edges(CurrentObjectGraph)) - {old(edge(o,f))}

    modifies o`fields
 {
  var cut := o.fields[f];
//   assert Valid();
//   //////reveal Valid();
//   assert
//     && (forall o <- CurrentObjectGraph :: o.Ready() && o.Valid())
//     && StandaloneObjectsAreValid(CurrentObjectGraph)
//     && OutgoingReferencesAreInTheseObjects(CurrentObjectGraph) 
//     && IncomingReferencesConstraintsOK(edges(CurrentObjectGraph)) 
//     ;


//   assert old(edges(CurrentObjectGraph)) == edges(CurrentObjectGraph);
  var more := old(edges(CurrentObjectGraph));
  var morp := partitionedIncomingEdges(more); 
// assert morpOK: morp == partitionedIncomingEdges(more);
//   assert OneOwnerIncoming(morp);

// assert (forall o <- morp.Keys :: 
//       (exists e <- morp[o] :: e.m.Owned?) ==> GroundSingleton(morp[o]));
  
// // forall  o <- morp.Keys 
// //   ensures ((exists e <- morp[o] :: e.m.Owned?) ==> ((|morp[o]|) <= 1))
// //   {
// //     if (exists e <- morp[o] :: e.m.Owned?) {
// //       assert GroundSingleton(morp[o]);
// //       SingletonIsSingleton(morp[o]);
// //      assert (|morp[o]|) == 1;
// //     }
// //   }

// // assert (forall o <- morp.Keys :: 
// //       (exists e <- morp[o] :: e.m.Owned?) ==> (|morp[o]|) <= 1);

// assert o.fieldModes[f].Owned?;   ///NOTE This is too tight in general...
// assert edge(o,f).m.Owned?;
// assert edge(o,f) in more;
// // assert (o.fields[f] in morp) && |morp[o.fields[f]]| == 1;
// assert (o.fields[f] in morp) ==> (edge(o,f) in morp[o.fields[f]]);

// assert forall e <- (edges(CurrentObjectGraph)) ::
//   (e.t == o.fields[f]) ==> ((e in morp[e.t]) && (e.f == o) && (e.n == f) && (e == edge(o,f)));

var CurrentEdgeSet := ( set e <- edges(CurrentObjectGraph) | e.t == (o.fields[f]));

// assert ObjectsToEdges(CurrentObjectGraph, more);


// assert o.fields[f] == cut;
// assert edge(o,f) in CurrentEdgeSet;

// //assert o.fieldModes[f].Owned? ==> (|CurrentEdgeSet| == 1);

//   //  if (o.fieldModes[f].Owned?) 
//   //    {
//   //      assert ObjectsToEdges(CurrentObjectGraph,edges(CurrentObjectGraph));
//   //      assert (|CurrentEdgeSet| == 1);
//   //      var edgeFromEdges : Edge := ExtractFromSingleton(CurrentEdgeSet);
//   //      assert edgeFromEdges.t == (o.fields[f]);
//   //      assert edgeFromEdges.f == o;
//   //      assert edgeFromEdges.n == f;
//   //      assert edgeFromEdges.m == o.fieldModes[f];
//   //      assert edgeFromEdges == edge(o,f);
//   //    }

//   ///////////////////////////////////////////////////////////////////
//   ///////////////////////////////////////////////////////////////////
// //  o.fields := RemoveKey(o.fields, f);
// //
// //
  //////reveal Valid();
 // assert forall o <- CurrentObjectGraph :: o.Ready() && o.Valid();
  var e, es1, es2 := LosingMyEdge(CurrentObjectGraph, o, f);


//   ///////////////////////////////////////////////////////////////////
//   ///////////////////////////////////////////////////////////////////


//   assert o.fields.Keys == old(o.fields.Keys) - {f};
//   assert old(o.fields.Keys <= o.fieldModes.Keys);
//   assert unchanged(o`fieldModes);
//   assert o.fieldModes == old(o.fieldModes);
//   assert o.fields.Keys <= o.fieldModes.Keys;
//   assert o.AllFieldsAreDeclared();

//   assert ObjectsToEdges({o}, edges({o}));
//   assert edges({o}) <= old(edges({o}));

//   assert old(edge(o,f)) == e;

//   assert o.Ready();
//   assert (o.region.World? || o.region.Heap?);  
//   assert o.OwnersValid();

//   assert f !in o.fields;
//   assert forall n <- o.fields :: n in old(o.fields);
//   assert forall n <- o.fields :: o.fields[n]==old(o.fields[n]) && o.fieldModes[n]==old(o.fieldModes[n]);
//   assert forall n <- o.fields :: AssignmentCompatible(o, o.fieldModes[n], o.fields[n]);
//   assert o.AllFieldsContentsConsistentWithTheirDeclaration();

//   assert o.Valid();

  var es := edges(CurrentObjectGraph);
//   assert whatthefuck: es == edges(CurrentObjectGraph);


//   assert forall o <- CurrentObjectGraph :: o.Ready() && o.Valid();
//  // assert es == edges(CurrentObjectGraph) by { //////reveal whatthefuck; }
//  assert es2 == es;
  // edgesWork(CurrentObjectGraph, es); 
  // edgesWorks2(CurrentObjectGraph, es);
  // assert ObjectsToEdges(CurrentObjectGraph, es);

//   assert forall e <- es :: not( e.f == o && e.n == f);
//   assert forall e <- es :: not( e.f == o && e.n == f && e.t == old(o.fields[f]) );

//   assert
//     && (forall o <- CurrentObjectGraph :: o.Ready() && o.Valid())
//     && OutgoingReferencesAreInTheseObjects(CurrentObjectGraph);

  var less := edges(CurrentObjectGraph);
  var lesp := partitionedIncomingEdges(less);

//   assert less <= more;
//   assert lesp == partitionedIncomingEdges(less);
//   assert morp == partitionedIncomingEdges(more);

  // FewerPartitionedIncomingEdgesValid(less, more, lesp, morp);

  // assert IncomingReferencesConstraintsOK(edges(CurrentObjectGraph)) 
  //   by { FewerPartitionedIncomingEdgesValid(less, more, lesp, morp); }

//   assert OneOwnerIncoming(lesp);
//   assert cut !in lesp || |lesp[cut]| == 0;
//   assert refCountEdges(cut, less) == 0;


  // assert Valid() by {
  //    //////reveal Valid();
  //    FewerPartitionedIncomingEdgesValid(less, more, lesp, morp);
  //    assert IncomingReferencesConstraintsOK(edges(CurrentObjectGraph));
  // }

//  assert e.t == cut;
//  assert o.fieldModes[f].Owned? ==> (forall e <- es2 :: e.t != cut );

//  //assert o.fieldModes[f].Owned? ==> (forall e <- edges(CurrentObjectGraph) :: e.t != cut );

//  //assert o.fieldModes[f].Owned? ==> (|(set  e <- edges(CurrentObjectGraph) :: e.t == (cut))| == 0);

}//end nul


// sets CurrentObjectGraph := os with os and x unchanged
method TRUMP(os : set<Object>, x : Object) 
  modifies this`CurrentObjectGraph
  ensures  CurrentObjectGraph == os
  ensures  forall o <- (os) :: unchanged(o)
  ensures unchanged(x)
{
  CurrentObjectGraph := os;
}

}






lemma PullingMyFuckingHairOut( o : Object, os : set<Object>)
  requires o in os
  ensures (os - {o}) < os
  ensures o !in (os - {o})
  ensures o in (os - {o}) + {o}
  ensures ((os - {o}) + {o}) == os
{}

lemma PullingMyFuckingHairOutAndIDontHaveMuchHair( o : Object, os : set<Object>)
  requires o in os
  ensures  (os - {o}) < os
  ensures  o !in (os - {o})
  ensures  o in (os - {o}) + {o}
  ensures  ((os - {o}) + {o}) == os

  requires && o.Ready() && o.Valid()
  requires forall x <- os - {o} :: && x.Ready() && x.Valid()
  ensures  forall x <- os       :: && x.Ready() && x.Valid()
{}

