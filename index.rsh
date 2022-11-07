'reach 0.1';

const[gameOutcome, F_WINS, Z_WINS, DRAW] = makeEnum(3);

const winner = (playHandF, playHandZ, gHandF, gHandZ)=> {
    if(gHandF == gHandZ){
        return DRAW;
    }
    else{
        if(gHandF == (playHandF + playHandZ)){
            return F_WINS;
        }
        else{
            if(gHandZ == (playHandF + playHandZ)){
                return Z_WINS;
            }
            else{
                return DRAW;
            }
        }
    }
};

assert(winner(0,4,0,4)== F_WINS);
assert(winner(4,0,4,0)== Z_WINS);
assert(winner(0,1,0,4)== DRAW);
assert(winner(5,5,5,5)== DRAW);

forall(UInt, a =>
    forall(UInt, b =>
    forall(UInt, c =>
    forall(UInt, d =>
    assert(gameOutcome(winner(a,b,c,d)))))));

    forall(UInt, a =>
        forall(UInt, b =>
        forall(UInt, c =>
        assert(winner(a,b,c,c) == DRAW))));

const Shared = {
    ...hasRandom,
    getHand: Fun([],UInt),
    getGuess: Fun([],UInt),
    seeOutcome: Fun([UInt], Null),
    informTimeout: Fun([],Null),
};

export const main = Reach.App(() =>{
    const Faizan = Participant('Faizan', {
        ...Shared,
        wager: UInt,
        deadline: UInt,
    });
    const Zaleha = Participant('Zaleha',{
        ...Shared,
        acceptWager: Fun([UInt],Null),
    });
    init();

    const informTimeout = () => {
        each([Faizan,Zaleha], () => {
            interact.informTimeout();
        });
    };

    Faizan.only(() => {
        const amt = declassify(interact.wager);
        const time = declassify(interact.deadline);
    });
    Faizan.publish(amt,time)
     .pay(amt);
    commit();

    Zaleha.interact.acceptWager(amt);
    Zaleha.pay(amt)
     .timeout(relativeTime(time), () => closeTo(Faizan, informTimeout));
     
    var outcome = DRAW;
    invariant(balance() == 2 * amt && gameOutcome(outcome));
    while(outcome == DRAW){
        commit();

        Faizan.only(() => {
            const _playHandF = interact.getHand();
            const _gHandF = interact.getGuess();

            const [_commitF,_saltF] = makeCommitment(interact,_playHandF);
            const commitF = declassify(_commitF);
            const[_guessCommitF, _guessSaltF] = makeCommitment(interact,_gHandF);
            const guessCommitF = declassify(_guessCommitF);
        });

        Faizan.publish(commitF, _guessCommitF)
         .timeout(relativeTime(time), () => closeTo(Zaleha, informTimeout));
        commit();

        unknowable(Zaleha, Faizan(_playHandF, _saltF));
        unknowable(Zaleha, Faizan(_gHandF, _guessSaltF));

        Zaleha.only(() =>{
            const _playHandZ = interact.getHand();
            const _gHandZ = interact.getGuess();
            const playHandZ = declassify(_playHandZ);
            const gHandZ = declassify(_gHandZ);
        });

        Zaleha.publish(playHandZ,gHandZ)
         .timeout(relativeTime(time), () => closeTo(Faizan, informTimeout));
        commit();

        Faizan.only(() => {
            const [saltF, playHandF] = declassify([_saltF, _playHandF]);
            const [guessSaltF, gHandF] = declassify([_guessSaltF,_gHandF]);
        })

        Faizan.publish(saltF, playHandF, guessSaltF, _gHandF)
         .timeout(relativeTime(time), () => closeTo(Zaleha, informTimeout));

        checkCommitment(commitF, saltF, playHandF);
        checkCommitment(guessCommitF, guessSaltF, gHandF);


      outcome = winner(playHandF, playHandZ, gHandF, gHandZ);
      continue;

    }//end of while loop
    assert(outcome == F_WINS || outcome == Z_WINS);
    transfer(2 * amt).to(outcome == F_WINS ? Faizan : Zaleha);
    commit();

    each([Faizan, Zaleha], () => {
        interact.seeOutcome(outcome);
    });
    exit();
});



