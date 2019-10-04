include "../circomlib/circuits/babyjub.circom";
include "../circomlib/circuits/comparators.circom";
include "../circomlib/circuits/poseidon.circom";
include "../circomlib/circuits/bitify.circom";
include "../circomlib/circuits/escalarmulfix.circom";
include "../circomlib/circuits/eddsaposeidon.circom";
include "../circomlib/circuits/smt/smtverifier_poseidon.circom";
include "../circomlib/circuits/smt/smtprocessor_poseidon.circom";
include "../circomlib/circuits/binsum.circom";

template NullifierMultisig(N) {

    signal input  commitment[N];
    signal input  nullifier[N];
    signal output success;

    component pvk2pbk[N];
    component pbkcheck[N];
    signal    count[N];

    for (var n=0;n<N;n+=1) {
        pvk2pbk[n] = BabyPbk();
        pvk2pbk[n].in <== nullifier[n];

        pbkcheck[n] = IsEqual();
        pbkcheck[n].in[0] <== pvk2pbk[n].Ax;
        pbkcheck[n].in[1] <== commitment[n];

        if (n == 0) {
            count[0] <-- pbkcheck[n].out;
        } else {
            count[n] <-- pbkcheck[n].out + count[n-1];
        }
    }

    component countcheck = IsEqual();
    countcheck.in[0] <== count[N-1];
    countcheck.in[1] <== N;

    success <== countcheck.out;
}


template FranchiseProof(nLevels, nAuth) {

    signal         input censusRoot;
    signal private input censusSiblings[nLevels];
    signal private input censusIdx;

    signal private input voteSigS;
    signal private input voteSigR8x;
    signal private input voteSigR8y;

    signal         input voteValue;

    signal private input privateKey;
    
    signal         input votingId;
    signal         input nullifier;

    signal         input gcommitment[nAuth];
    signal private input gnullifier[nAuth];

    component gnullcheck = NullifierMultisig(nAuth);
    for (var n=0;n<nAuth;n+=1)  {
        gnullcheck.commitment[n] <== gcommitment[n];
        gnullcheck.nullifier[n] <== gnullifier[n];
    }

    signal verify;
    verify <-- 1 - gnullcheck.success; 

    // -- extract public key -------------------------------------------
    component pbk = BabyPbk();
    pbk.in <== privateKey;

    // -- verify vote signature  ---------------------------------------
    component sigVerification = EdDSAPoseidonVerifier();
    sigVerification.enabled <== verify;

    // signer public key (extract from private key)
    sigVerification.Ax <== pbk.Ax;
    sigVerification.Ay <== pbk.Ay;

    // signature (coordinates)
    sigVerification.S <== voteSigS;
    sigVerification.R8x <== voteSigR8x;
    sigVerification.R8y <== voteSigR8y;

    // message
    sigVerification.M <== voteValue;

    // -- verify public key is in census merkle tree ---------------------
    
    component smtCensusInclusion = SMTVerifier(nLevels);
    smtCensusInclusion.enabled <== verify;

    // check for inclusion (0 => VERIFY INCLUSION, 1=>VERIFY EXCLUSION)
    smtCensusInclusion.fnc <== 0;

    // *old* parameters are not used (only works for EXCLUSION case)
    smtCensusInclusion.oldKey <== 0;
    smtCensusInclusion.oldValue <== 0;
    smtCensusInclusion.isOld0 <== 0;

    // root and siblings
    smtCensusInclusion.root <== censusRoot;
    for (var i=0; i<nLevels; i+=1) {
        smtCensusInclusion.siblings[i] <==  censusSiblings[i];
    }

    // key and value 
    smtCensusInclusion.key <== censusIdx;

    component hashAxAy = Poseidon(2,6,8,57);
    hashAxAy.inputs[0] <== pbk.Ax;
    hashAxAy.inputs[1] <== pbk.Ay;
    smtCensusInclusion.value <== hashAxAy.out;

    // -- verify nullifier integrity -----------------------------------
    component hashPvkVid = Poseidon(2,6,8,57);
    hashPvkVid.inputs[0] <== privateKey;
    hashPvkVid.inputs[1] <== votingId ;
    
    component nullifierCheck = ForceEqualIfEnabled();
    nullifierCheck.enabled <== verify;
    nullifierCheck.in[0] <== nullifier;
    nullifierCheck.in[1] <== hashPvkVid.out;

}

#[test]
template test_voting_20() {
    component main = FranchiseProof(20);

    #[w] {
        main.privateKey <== 3876493977147089964395646989418653640709890493868463039177063670701706079087;
        main.votingId <== 1;
        main.nullifier <== 18570357092029990534015153781798290815577397208925401637716365342267062658897;
        main.censusRoot <== 15628532949280720223077383407297400734969515772490239240715135787382227308157;
        for (var n=0;n<20;n+=1) {
            main.censusSiblings[n] <== 0;
        }
        main.censusIdx <== 1337;
        main.voteSigS <== 2049495377478274326519165466593378972734554211375612654402604012080164390815;
        main.voteSigR8x <== 14670348391137384574095265741371426216865551653599272344433977096828239606867;
        main.voteSigR8y <== 14049142839519357696409855481674224186117305076655920589500172245054519140805;
        main.voteValue <== 2;
        main.gcommitment[0] <== 16508917144752610602145963506823743115557101240265470506805505298395529637033;
        main.gcommitment[1] <== 1891156797631087029347893674931101305929404954783323547727418062433377377293;
        main.gnullifier[0] <== 0;
        main.gnullifier[1] <== 0;
    }
}

component main = FranchiseProof(20);
