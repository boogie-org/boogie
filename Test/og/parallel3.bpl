procedure {:entrypoint} {:yields} main() 
{
    call A() | B();
}

procedure {:yields} {:stable} A() {}
procedure {:yields} {:stable} B() {}
