import { loadStdlib, ask } from "@reach-sh/stdlib";
import * as backend from './build/index.main.mjs';
const stdlib = loadStdlib();

const isFaizan = await ask.ask(
    `Are you Faizan?`,
    ask.yesno
);
const who = iFaizan ? 'Faizan' : 'Zaleha';
console.log(`Starting Morra games! as ${who}`);

let acc = null;
const createAcc = await ask.ask(
    `Would you like to create an account? (only possible on devnet)`,
    ask.yesno
);
if(createAcc){
    acc = await stdlib.newTestAccount(stdlib.parseCurrency(1000));
}
else{
    const secret = await ask.ask(
    `What is your account secret?`,
    (x => x)
    );
    acc = await stdlib.newAccountFromSecret(secret);
}

let ctc = null;
if(isFaizan){
    ctc = acc.contract(backend);
    ctc.getInfo().then((info) => {
        console.log(`The contract is deployed as = ${JSON.stringify(info)}`);});
}else{
    const info = await ask.ask(
        `Please paste the contract information: `,
        JSON.parse
    );
    ctc = acc.contract(backend, info)
}

const fmt = (x) => stdlib.formatCurrency(x,4);
const getBalance = async () => fmt(await stdlib.balanceOf(acc));

const before = await getBalance();
console.log(`Your balance is ${before}`);

const interact = {...stdlib.hasRandom };

interact.informTimeout = () => {
    console.log(`There was a timeout.`);
    process.exit(1);
};

if(isFaizan){
    const amt = await ask.ask(
        `How much do you want to wager?`,
        stdlib.parseCurrency
    );
    interact.wager = amt;
    interact.deadline = { ETH: 100, ALGO: 100, CFX: 1000}[stdlib.connector];
}else{
    interact.acceptWager = async (amt) => {
        const accepted = await ask.ask(
            `Do you accept the wager of ${fmt(amt)}?`,
            ask.yesno
        );
        if(!accepted){
            process.exit(0);
        }
    };
}

const HANDS = [0, 1, 2, 3, 4, 5];
//getHand()
interact.getHand = async () => {
    const hand = await ask.ask(`What hand will you play?`, (x) =>{
        const hand = HANDS[x];
        if(hand === undefined){
            throw Error(`Not a valid hand ${hand}`);
        }
        return hand;
    });
    console.log(`You played ${HANDS[hand]}`);
    return hand;
};
 
 const GUESS = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];  
 interact.getGuess = async () => {
    const guess= await ask.ask(`Guess the hand?`, (x) =>{
        const guess = GUESS[x];
        return guess;
    });
    console.log(`You guess ${GUESS[guess]}`);
    return guess;
};

//outcome function
const OUTCOME = ['Zaleha wins', 'Draw', 'Faizan wins'];
interact.seeOutcome = async (outcome) => {
    console.log(`The outcome is: ${OUTCOME[outcome]}`);
};

//participant
const part = iFaizan ? ctc.pFaizan : ctc.p.Zaleha;
await part(interact);

const after = await getBalance();
console.log(`Your balance is now ${after}`);

ask.done()