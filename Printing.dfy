


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





