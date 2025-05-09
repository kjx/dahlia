//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// edges
//////////////////////////////////////////////////////////////////////////////
//
// some computations work with sets of edges, instead of sets of objects
// methods like edges(oo:set<Object>) or incomingEdges(o:Object)
// "generate" the edge-sets as needed
//
// one edge is pretty much a named tuple for a single edge
// f=from object, n=field name in f, t=to object

datatype Edge = Edge(f : Object, n : string, m : Mode, t : Object)


//messier than I would like...
//all edges generated by os.
//destintaions not necessarily in os
  function edges(os : set<Object>) : (r : set  <Edge>)
   // reads (set o <- os, o2 <- o.ValidReadSet() :: o2)
   // requires forall o <- os :: o.Ready() && o.Valid()
   // reads os`fields, os`fieldModes
   reads os
  {
     set o <- os, n <- o.fields
       |  n in o.fieldModes
       :: Edge(o, n, o.fieldModes[n], o.fields[n])
  }


  /*opaque*/ function edge(o : Object, n : string) : (e : Edge)   //set or singleton?
   reads o
   requires n in o.fieldModes && n in o.fields
   ensures  e == Edge(o, n, o.fieldModes[n], o.fields[n])
  {
    Edge(o, n, o.fieldModes[n], o.fields[n])
  }


  function edgesFromObjectFields(o : Object, ns : set<string>) : (r : set  <Edge>)
   reads o
  {
     set n <- ns
       |  n in o.fieldModes &&  n in o.fields
       :: Edge(o, n, o.fieldModes[n], o.fields[n])
  }

  function edgesViaEFO(os : set<Object>) : (r : set  <Edge>)
    reads os
    { set o <- os, e <- edgesFromObject(o) :: e }


  function edgesFromObject(o : Object) : (r : set  <Edge>)
//   ensures r == edges({o})
   reads o
  {
     set n <- o.fields
       |  n in o.fieldModes // &&  n in o.fields
       :: Edge(o, n, o.fieldModes[n], o.fields[n])
  }



//standalone lemma saying what edges does.
//aim is to avoid cluttering Dafny with crud every time we use "edges"
//but to have all the stuff around if needed
//HMMM: ObjctsToEdges below seems more concise & more useful...
lemma {:foo} edgesWork(os : set<Object>, r : set  <Edge>)
  requires forall o <- os :: o.Ready() && o.Valid() //DO I want this or not? or a separate lemma
  requires r == edges(os)
  ensures forall edge <- r :: edge.n in edge.f.fields && edge.f.fields[edge.n] == edge.t
  ensures (os == {}) ==> (r == {})
  ensures forall o <- os, n <- o.fields ::
        && (n in o.fieldModes.Keys) //added for bug in 4.9.2
        && (Edge(o, n, o.fieldModes[n], o.fields[n]) in r)
  ensures forall e <- edges(os) :: (e.f in os) && (e.n in e.f.fields) && (e.m == e.f.fieldModes[e.n]) && (e.t == e.f.fields[e.n])
  //ensures OutgoingReferencesAreInTheseObjects(os) ==> AllThoseEdgesAreWthinTheseObjects(os,r)
  ensures forall edge <- r :: (edge.f in os)
  ensures OutgoingReferencesAreInTheseObjects(os) ==> (forall edge <- r :: (edge.t in os))
  ensures OutgoingReferencesAreInTheseObjects(os) ==> (e2o(r) <= os)
{}

lemma {:foo} edgesWorks2(os : set<Object>, es : set  <Edge>)
  requires forall o <- os :: o.Ready() && o.Valid()
  requires es == edges(os)
{
   edgesWork(os,es);
   var incoming := partitionedIncomingEdges(es);

  assert forall o <- os, n <- o.fields :: (Edge(o, n, o.fieldModes[n], o.fields[n]) in incoming[ o.fields[n] ]);
  assert forall t <- incoming.Keys, e : Edge  <- incoming[t] ::
     (e.f in os) && (e.n in e.f.fields) && (e.m == e.f.fieldModes[e.n]) && (e.t == e.f.fields[e.n]);
}



predicate ObjectsToEdges(os : set<Object>, es : set<Edge>)
  reads os + (set o <- os, v <- o.ValidReadSet() :: v) + (set o <- os, v <- o.fields.Values :: v) + (set e <- es :: e.f) + (set e <- es :: e.t)
  requires forall o <- os :: o.Ready() && o.Valid() //DO I want this or not? or a separate lemma
//   requires es == edges(os)
{
 assert forall o <- os :: o.Ready() && o.Valid();

  && (forall e <- es :: e.n in e.f.fields && e.f.fields[e.n] == e.t)
  && ((os == {}) ==> (es == {}))
  && (forall o <- os, n <- o.fields :: (Edge(o, n, o.fieldModes[n], o.fields[n]) in es))
  && (forall e <- es :: (e.f in os) && (e.n in e.f.fields) && (e.m == e.f.fieldModes[e.n]) && (e.t == e.f.fields[e.n]))
}

lemma ObjectsToEdgesEquals(os : set<Object>, es1 : set<Edge>, es2 : set<Edge>)
  requires forall o <- os :: o.Ready() && o.Valid()
  requires ObjectsToEdges(os,es1)
  requires ObjectsToEdges(os,es2)
  ensures  es1 == es2
{}





function incomingModesEdges(es : set<Edge>) : (rv : set<Mode>)
{
  set e <- es :: e.m
}


predicate edgesAreConsistentWithDafnyHeap(es : set<Edge>)
//  reads set e <- es, x <- {e.f, e.t} :: x
reads set e <- es :: e.f
//reads set e <- es :: e.t //do I need this
 {
  true
 }






function outgoingEdges(f : Object, edges : set<Edge>) : (rs : set<Edge>)
  ensures rs <= edges
{
  set e <- edges | e.f == f
}


function incomingEdges(t : Object, edges : set<Edge>) : (rs : set<Edge>)
  ensures rs <= edges
{
  set e <- edges | e.t == t
}


function refCountEdges(t : Object, edges : set<Edge>) : nat
{
  | incomingEdges(t, edges) |
}


lemma fieldEdgesAreOutgoing(os : set<Object>)
  requires forall o <- os :: o.Ready() && o.Valid()
  ensures
      var edges := edges(os);
      && (forall e <- edges :: e.f.fields[e.n] == e.t)
      && (forall o <- os, n <- o.fields ::
        && (n in o.fieldModes.Keys) //added for bug in 4.9.2
        && (Edge(o, n, o.fieldModes[n], o.fields[n]) in edges))
{}

 lemma edgesFromDisjointObjects(aa : set<Object>, bb : set<Object>)
      requires forall o <- (aa + bb) :: o.Ready() && o.Valid()
      requires aa !! bb
      ensures
        edges(aa + bb) == edges(aa) + edges(bb)
{}

//NOTe  this seems to be correct a far as I can tell -
//verifies fine on the command line but not in the IDE!
//but NOT ACTUALLY USED!
 lemma {:verify false} edgesFromWholeSetOfSetsOfDisjointObjects(ooo : set<set<Object>>)
      requires forall oo <- ooo, o <- oo :: o.Ready() && o.Valid()
      requires forall aa <- ooo, bb <- ooo :: aa !! bb
      ensures  forall oo <- ooo, o <- oo :: o.Ready() && o.Valid()
      ensures  forall aa <- ooo, bb <- ooo :: aa !! bb
      ensures
        edges(set oo <- ooo, o <- oo :: o)
          == (set oo <- ooo, e <- edges(oo) :: e)
      ensures
        edges(set oo <- ooo, o <- oo :: o)
          == (set oo <- ooo, o <- oo, e <- edges({o}) :: e)
      ensures
          (set oo <- ooo, e <- edges(oo) :: e)
          == (set oo <- ooo, o <- oo, e <- edges({o}) :: e)

{
      assert
          (set oo <- ooo, e <- edges(oo) :: e)
          == (set oo <- ooo, o <- oo, e <- edges({o}) :: e);

      assert
        edges(set oo <- ooo, o <- oo :: o)
          == (set oo <- ooo, e <- edges(oo) :: e);
      assert
        edges(set oo <- ooo, o <- oo :: o)
          == (set oo <- ooo, o <- oo, e <- edges({o}) :: e);

}




//all objects FROM whcih edges leave in the edge-set
function {:todo "horible name"} FromObjectsEdges(es : set<Edge>) : set<Object> {
  set e <- es :: e.f
}






lemma fewerEdgesLowerRefCounts(fewer : set<Edge>, extra : set<Edge>, os : set<Object>)
  requires fewer !! extra
  ensures forall o <- os :: refCountEdges(o, fewer) <= refCountEdges(o, fewer + extra)
{
RefCountDistributesOverDisjointEdges(os, fewer, extra);
}



lemma fewerEdgesFewerIncomers(fewer : set<Edge>, extra : set<Edge>, os : set<Object>)
  requires fewer !! extra
  ensures forall o <- os :: incomingEdges(o, fewer) <= incomingEdges(o, fewer + extra)
{
RefCountDistributesOverDisjointEdges(os, fewer, extra);
}


lemma fewerEdgesFewerOutgoings(fewer : set<Edge>, extra : set<Edge>, os : set<Object>)
  requires fewer !! extra
  ensures forall o <- os :: outgoingEdges(o, fewer) <= outgoingEdges(o, fewer + extra)
{
RefCountDistributesOverDisjointEdges(os, fewer, extra);
}


//kjx need to sort out API , is it he fewer + extra, or fewer vs more?
//ie are they disjoint, or what...
//os comes first or last
lemma fewerEdgesPreservesShit(fewer : set<Edge>, extra : set<Edge>, os : set<Object>)
  requires fewer !! extra
 // ensures forall o <- os :: refCountEdges(o, fewer) <= refCountEdges(o, fewer + extra)
{
RefCountDistributesOverDisjointEdges(os, fewer, extra);
}


//KJX shit wiull we hace to worry avout outside & iunside or Regions as well as Objecs???


  function externalEdges(o: Object, edges : set<Edge>) : (rs : set<Edge>)
  // all edges comin into O from objects outside.
  //KJX is this right?  will it do what we want?
    ensures rs <= edges
    reads e2o(edges)
  {
    set e <- edges | outside(e.f, o) && inside(e.t, o)

//KJX or  set e <- edges | e.f.outside(o) && e.t.inside(o)
//  part.inside(whole), or
//  whole.owns(part) ...       --- but what's that mean with multiple owners?
//  whole.contains(part) ...   --- but what's that mean with multiple owners?
  }






// currently unused (mostlty) AND not clear how to genrealise to multiple owners
// maybe this isn't waht we want" waht we want is just a coHeap?
//
// //abbrev for heapExternalEdgesPartitionedByOwners - which I don't need right now
//   function HxR(edges : set<Edge>) : map<Owners,set<Edge>>
//      reads e2o(edges)
//   {
//     heapExternalEdgesPartitionedByOwners(edges)
//   }

//   function heapExternalEdgesPartitionedByOwners(edges : set<Edge>) : map<Owners,set<Edge>>
//    reads e2o(edges)
//   {
//     var heapExternalEdges := justHeapExternalEdges(edges);
//     var allRelevantHeapOwnerss := set he : Edge <- heapExternalEdges :: he.t.owners();
//     map r : Owners <- allRelevantHeapOwnerss :: externalEdges(r, heapExternalEdges)
//   }


//or should this be "allExternalEdges"
//went with "just" with the idea "justX(a):r" means to filter ---- ensures r <= a
//meanwhile allX(a):r can do move - e.g. map all objects to all owning "ownerss"
///*opaque*/
//
//KJX Sept 2024- what the HELL is is trying'' to do?
//KJS is this right?
function justHeapExternalEdges(edges : set<Edge>) : (rs : set<Edge>)
    ensures rs <= edges
//redundant    ensures (set e <- rs :: e.t.owner) <=  (set e <- edges :: e.t.owner)
    ensures (forall e <- rs :: e.f.owner != e.t.owner)
    ensures (forall e <- edges :: (((e.f.owner != e.t.owner)) ==> (e in rs)))
//redundant        ensures (forall e <- rs :: e in edges)
    ensures (forall e <- edges :: (e.f.owner != e.t.owner )) ==> (edges == rs)
    ensures (forall e <- edges :: (e.f.owner == e.t.owner))  ==> (rs == {})

   // reads e2o(edges)`owners
  {
    set e <- edges | e.f.owner != e.t.owner
//  set e <- edges | e.f.allExternalOwners() != e.t.allExternalOwners()
  }

predicate e2oRV(edges : set<Edge>)
// reads (set o <- e2o(edges), o2 <- o.ValidReadSet() :: o2)
 reads var ee := set o <- e2o(edges);  ee`fields
 reads var ee := set o <- e2o(edges);  ee`fieldModes
 {

  forall e <- edges :: e.f.Ready() && e.f.Valid()
                    && e.t.Ready() && e.t.Valid()
}

function e2o(edges : set<Edge>) : (rx : set<Object>)
{
(set e <- edges :: e.f) + (set e <- edges :: e.t)
}
//should this be called segde? -it's pretty much the inverse of edges.  kinda.

lemma e2oMonotonic(less : set<Edge>, more : set<Edge>)
     requires less <= more
     ensures  e2o(less) <= e2o(more)
     ensures (set o <- e2o(less), o2 <- o.ValidReadSet() :: o2) <= (set o <- e2o(more), o2 <- o.ValidReadSet() :: o2)
{}


lemma o2e2o(os : set<Object>, es : set<Edge>)
  requires es == edges(os)
  requires forall o <- os :: o.Ready() && o.Valid() //hmm shojld that be a precondition or antecedent?

  // requires forall e <- es :: e.f in os
  // ensures forall e <- es :: e.f in os
  ensures OutgoingReferencesAreInTheseObjects(os) ==> (e2o(es) <= os)
  ensures OutgoingReferencesAreInTheseObjects(os) ==> (forall o <- e2o(es) :: o.Ready() && o.Valid())
{
  assert forall e <- es :: e.f in os;
  assert OutgoingReferencesAreInTheseObjects(os) ==>  forall e <- es :: e.t in os;
}








//need to describe this properly
method LosingMyEdge(os : set<Object>, o : Object, n : string)
  returns (e : Edge, es1 : set<Edge>, es2 : set<Edge>)

  requires forall o <- os :: o.Ready() && o.Valid()
  requires o in os
  requires n in o.fields

  modifies o`fields

  ensures forall o <- os :: o.Ready() && o.Valid()
  ensures es1 == old(edges(os))
  ensures old(ObjectsToEdges(os,es1))
  ensures es2 == edges(os)
  ensures ObjectsToEdges(os,es2)
  ensures o.fields == old(RemoveKey(o.fields,n))
  ensures e == old(edge(o,n))
  ensures es2 == es1 - {e}

  ensures n !in o.fields.Keys
{
 es1 :=  edges(os);
 assert ObjectsToEdges(os,es1);

 e := edge(o,n);

 o.fields := RemoveKey(o.fields,n);

ALLFEWERFIELDS(os);
 assert forall o <- os :: o.Ready() && o.Valid();

 es2 := edges(os);
 assert ObjectsToEdges(os,es2);
}
