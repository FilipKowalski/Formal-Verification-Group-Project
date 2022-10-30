predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || !(forall x :: (0 <= x < |pre|) ==> (pre[x] == str[x]))
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

predicate isSubstringPred(sub:string, str:string)
{
	(|sub| <= |str|) && exists i :: (0 <= i < |str|-|sub|) && isPrefixPred(sub, str[i..])
}


predicate isNotSubstringPred(sub:string, str:string)
{	
	forall i :: (0 <= i < |str|-|sub|) ==> isNotPrefixPred(sub, str[i..]) || !(|sub| <= |str|)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

//ALL OF THE ABOVE TOOK ABOUT 1 HOUR

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
  //TODO
  exists i,j :: 0 <= i <= |str1|-k && j == i+k && isSubstringPred(str1[i..j],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	//TODO: your FOL formula should start with a forall
	forall i,j :: 0 <= i <= |str1|-k && j == i+k ==> isNotSubstringPred(str1[i..j],str2)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}