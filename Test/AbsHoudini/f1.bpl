var g: int;

procedure {:entrypoint} main()
  modifies g;
{
   var x: int;
   var c: bool;

   g := 1;
  
   if(c) {
     g := g + 1;
   } else {
     g := 3;
   }

   call foo();

   if(old(g) == 0) { g := 1; }
}

procedure foo() 
  modifies g;
{
  g := g + 1;
}

procedure {:template} summaryTemplate();
  ensures {:post} g == old(g) + 1;
  ensures {:post} g == old(g) + 2;
  ensures {:post} g == old(g) + 3;
  ensures {:pre} old(g) == 0;
