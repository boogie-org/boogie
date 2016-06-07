procedure {:checksum "0"} M();

implementation {:id "M"} {:checksum "1"} M()
{
    if (*)
    {
        assert {:subsumption 0} 1 != 1;  // error
    }
    else if (*)
    {
        assert {:subsumption 1} 5 != 5;  // error
    }
    else if (*)
    {
        assert {:subsumption 2} 6 != 6;  // error
    }
    else
    {
        assert {:subsumption 1} 2 == 2;
        assert {:subsumption 2} 4 == 4;
        assert 5 == 5;
    }

    assert {:subsumption 0} 3 == 3;
}
