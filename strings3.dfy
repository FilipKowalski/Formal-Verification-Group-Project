predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	// now that i know more about dafny i could rewrite my original to be much cleaner
	if (|pre| > |str|) {
		return false;
	}

	if (|pre| == 0) {
		return true;
	}

	return (pre == str[..|pre|]); 
    
}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	//assume false try prove true
	res := false;

	if (|sub| > |str|) {
		return false;
	}

	var i := 0;
	// the reason this loop is i <= |str| is because we need to check the empty sequence given by str[..|str|]
	while (i <= |str| && res == false && |str[i..]| >= |sub|) 
	invariant 0 <= i <= |str| + 1
	invariant (forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])) <==> res == false
	decreases |str| - i;
	{
		res := isPrefix(sub, str[i..]);
		i := i + 1;
	}
	return res;
}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	//assume false try to prove true
	found := false;
	if (k > |str1| || k > |str2|) {
		return found;
	}

	//check each k substring in string 1 to each k substring in string 2
	var i := 0;
	while (i <= |str1| - k && found == false)
    invariant 0 <= k <= |str1|
    invariant 0 <= i <= |str1| - k + 1
	invariant (forall j, y :: 0 <= j < i && y == j + k ==> isNotSubstringPred(str1[j..y], str2)) <==> found == false
	decreases |str1| - i
	{
		found := isSubstring(str1[i..i+k], str2);
		i := i + 1;
	}
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
	//start with max length size str1
	len := |str1|;
	while(len > 0)
		invariant forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2)
		decreases len
	{
		var kSubsRes := haveCommonKSubstring(len, str1, str2);
		if kSubsRes{ return len;}
		len := len - 1;
	}//if not found then exit loop len=0
	assert isPrefixPred(str1[0..0], str2[0..]);//for len=0 
	return len;
}


