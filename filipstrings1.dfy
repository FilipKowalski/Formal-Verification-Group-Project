method isPrefix(pre: string, str: string) returns (res:bool) {
    //assume is a prefix, set to false if pre is longer than str
    //set to false if we encounter a character and idx i in pre that
    //doesnt match the character at idx i of str
    res := true;
    if (|pre| > |str|) {
        res := false;
    }
    else {
        var i := 0;
        while (i < |pre|) 
            invariant i >= 0;
        {
            if (pre[i] != str[i]) {
                res := false;
            }
            i := i + 1;
        }
    }
}

method isSubstring(sub: string, str: string) returns (res:bool) {
    res := false;
    if (|sub| == 0) {
        res := true;
    }
    var i := 0;
    var j := 0;
    while (i <= |str| - |sub|) 
        invariant i >= 0;
    {
        j := 0;
        var count := 0;
        while (j < |sub|) 
            invariant j >= 0;
        {
            if (str[i + j] == sub[j]) {
                count := count + 1;
            }
            if (count == |sub|) {
                res := true;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool) {
    var i := 0;
    found := false;
    var tempFound := false;
    while (i < |str1| - k)
        invariant i >= 0
    {
        tempFound := isSubstring(str1[i..i+k], str2);
        if (tempFound == true) {
            found := true;
        }
        i := i + 1;
    }
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat) {
    var i := 0;
    var hasSub := false;
    while (i < |str1|) 
        invariant i >= 0
    {
        hasSub := haveCommonKSubstring(i, str1, str2);
        if (hasSub) {
            len := i;
        }
        i := i + 1;
    }
}