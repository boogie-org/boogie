procedure {:entrypoint} {:yields} main() 
{
    par A() | B();
}

procedure {:yields} {:stable} A() {}
procedure {:yields} {:stable} B() {}
