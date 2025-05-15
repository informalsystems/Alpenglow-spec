// -*- mode: Bluespec; -*-

module consensus {

  import anden.* from "./anden"
//
// Consensus / State machine interface CSMI
// functional side
//
// Here one needs to specify 
// - the types: ProcessID, LocalState, Message, TimeoutEvent, ConsensusOutput
// - the functions: initialize_process, receive_message, fire_timeout_event (that define the
//   message handlers and timeout handlers of the algorithm)  
//

// CSMI-TODO
type ProcessID

// CSMI-TODO
// type LocalState = Slot -> SlotState



// CSMI-TODO
// type Message =
//   // CSMI-TODO: add here the message types of the algorithm
//   // e.g. Proposal, Prevote, Precommit, etc.
//   | Propose // this could carry data in an argument

// CSMI-TODO
type TimeoutEvent
  // CSMI-TODO: add here the timeout types of the algorithm
  // e.g. TimeoutPrevote, TimeoutPrecommit, etc.

// CSMI-TODO
// type ConsensusOutput = 
//   | Broadcast(Message)
//   // CSMI-TODO: add here the output types of the algorithm
//   // e.g. SendMessageTo, BroadCastProposal, etc.

// type ConsensusResult = {
//   output: Set[ConsensusOutput],
//   state: LocalState,
// }


// CSMI-TODO 
// This initializes process that is identified by ProcessID
pure def initialize_process (id: ProcessID): LocalState =
  { Map() } // CSMI-TODO: add more here



// // CSMI-TODO
// // This is the function that contains all the message handlers of the algorithm
// pure def receive_message(state: LocalState, msg: Message): ConsensusResult =
//   // CSMI-TODO: add here the message handlers of the algorithm
//   // e.g. if msg leads to sending another message m, then add a corresponding entry to output
//   // and return the new state of the node
//   match msg {
//     | Propose => { state: state, output: Set() } // CSMI-TODO: add more here
//   }



// // CSMI-TODO
// // This is the function that contains all the timeout handlers of the algorithm
// pure def fire_timeout_event(state: LocalState, timeout: TimeoutEvent): ConsensusResult =
//   // CSMI-TODO: add here the timeout handlers of the algorithm
//   // e.g. if timeout leads to go to a new round and send a message m, then 
//   // return the state of the node with the new round number and add an entry for sending the
//   // message to output
//   { state: state, output: Set() }

// End of CSMI functional side




//
// Add here the types and functions that are needed for the consensus algorithm
//


//
//
// State machine
//
//


const correct: Set[ProcessID] // set of correct processes (non Byzantine)
const byzantine: Set[ProcessID] // set of Byzantine processes

const blocks: Set[Block] // set of blocks

// Assumption 1
assume correct.size() > byzantine.size() * 4 // N > 5F

// Assumption 2 on additional crashes: TODO

val sixty = correct.union(byzantine).size() * 60 / 100
val eighty = correct.union(byzantine).size() * 80 / 100

type NetWorkMsg = {
  sender: ProcessID,
  msg: Message,
}

type Environment = {
  system: ProcessID -> LocalState,
  now: Slot, // we can push to different views of slots later
  msgBuffer: Set[NetWorkMsg],
  activeTimeouts: ProcessID -> Set[TimeoutEventData], 
}

var s: Environment

//
//
// Consensus / State machine interface CSMI
// effect side
//
//


// CSMI-TODO 
// This specification is event triggered, so a process step can only be triggered by a message or a timeout
// as a result we need either messages or timeouts in the initial state
pure def initial_global_state: Environment =
  { system: correct.mapBy(v => initialize_process(v)),
    slot: 0,
    msgBuffer: Set(),
    activeTimeouts: correct.mapBy(v => Set()),
  }


// CSMI-TODO
/// Interface consensus algorithm / state machine: how consensus algorithm effects the environment 
pure def apply_effect (env: Environment, v: ProcessID, res: Result): Environment =
  val new = { ... env, system: env.system.set(v, res.post) } // update the state of the process
  res.output.fold(new, (s, o) => 
    match o {
      | Broadcast(msg) => 
        val nm = { sender: v, msg: msg }
        { ... s, msgBuffer: s.msgBuffer.union(Set(nm))} // add the message to the buffer
      | ScheduleEventTimeout(slot) =>
        { ... s, activeTimeouts: s.activeTimeouts.set(v, s.activeTimeouts.get(v).union(Set(slot))) } // add the timeout to the buffer
    })



  
  


// end of CSMI effect side


//
// General state machine
//

action init = all {
  s' = initial_global_state
}


action receive_block(v: ProcessID): bool = all{
  nondet block = blocks..filter(b => b.slot == s.now).oneOf()
  val result = consensus(s.system.get(v), BlockCI(block))
  s' = apply_effect(s, v, result)
}

action fire_timeout_event(v: ProcessID): bool = all{
    nondet timeout = oneOf(s.activeTimeouts.get(v))
    val s2 = { ... s, activeTimeouts: s.activeTimeouts.set(v, s.activeTimeouts.get(v).exclude(Set(timeout))) }
    val result = consensus(s2.system.get(v), TimeOutCI(timeout))
    s' = apply_effect(s2, v, result)
}

pure def NotarizedBlocks (msgs: Set[NetWorkMsg]): Set[{slot: Slot, hash: Blockhash}]= 
  pure def block_notarized(slot: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): bool = 
    msgs.filter(m => m.msg ==  NotarVoteMsg({slot: slot, hash: hash}))
        .size() >= sixty 
  msgs.fold(Set(), (s, x) => match x.msg {
                          | NotarVoteMsg(m) => s.union(Set(m))
                          | _ => s
                        })
              .filter(t => block_notarized(t.slot, t.hash, msgs))

pure def NotarFallBackBlocks (msgs: Set[NetWorkMsg]): Set[{slot: Slot, hash: Blockhash}]= 
  pure def block_notarized(slot: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): bool = 
    msgs.filter(m =>  m.msg ==  NotarVoteMsg({slot: slot, hash: hash}) or 
                      m.msg ==  NotarFallBackVoteMsg({slot: slot, hash: hash}) )
        .size() >= sixty 
  msgs.fold(Set(), (s, x) => match x.msg {
                          | NotarVoteMsg(m) => s.union(Set(m))
                          | NotarFallBackVoteMsg(m) => s.union(Set(m))
                          | _ => s
                        })
              .filter(t => block_notarized(t.slot, t.hash, msgs))

pure def SlotSkipCertified (msgs: Set[NetWorkMsg]): Set[Slot]= 
  pure def slot_skip_certified(slot: Slot, msgs: Set[NetWorkMsg]): bool = 
      msgs.filter(m => m.msg == SkipVoteMsg(slot))
          .size() >= sixty 
  msgs.fold(Set(), (s, x) => match x.msg {
                          | SkipVoteMsg(m) => s.union(Set(m))
                          | _ => s
                        })
              .filter(t => slot_skip_certified(t, msgs))

/// Definition 16
// Warning "notarization or notar-fallback": notar-fallback seems to imply notar
// Warning: Previous block? Block for previous slot
pure def ParentReadyP (s: Slot, hash: Blockhash, msgs: Set[NetWorkMsg]): bool = all {
  first_slot_in_leader_window(s),
  val nbset = NotarizedBlocks(msgs).filter(t => t.hash == hash)
  // TODO notarfallback missing
  all {
    nbset.size() > 0, // there is at least one notarized block
    nbset.getOnlyElement().slot.to(s).subseteq(SlotSkipCertified(msgs))
    // all intermediate slots are skip certified
  }

}

action BlockNotarizedAction(v: ProcessID): bool = all {
  nondet notarized = NotarizedBlocks(s.msgBuffer).oneOf()
  s' = apply_effect(s, v, consensus(s.system.get(v), BlockNotarizedCI(notarized)))
}

action ParentReadyAction(v: ProcessID): bool = all {
  nondet b = blocks.filter(b=> ParentReadyP(now, b.hash, s.msgBuffer)).oneOf()
  s' = apply_effect(s, v, consensus(s.system.get(v), ParentReadyCI({slot: now, hash: b.hash})))
}

action step = 
  nondet v = oneOf(correct)
  any {
    receive_block(v),
    fire_timeout_event(v),
    BlockNotarizedAction(v),
    s' = { ... s, now: s.now + 1 }, // increment the slot
  }


//
// Standard interleaving semantics (one process receives one message/timeout in one action)
//

// pure def receive_one_message (state: Environment, v: ProcessID, msg: Message): Environment =
//   val consumed_msg_state = { ... state, msgBuffer: state.msgBuffer.set(v, state.msgBuffer.get(v).exclude(Set(msg))) }
//   val res = state.system.get(v).receive_message(msg)
//   apply_effect(state, v, res)


// pure def fire_one_timeout_event (state: Environment, v: ProcessID, timeout: TimeoutEvent): Environment =
//   val consumed_timeout_state = { ... state, activeTimeouts: state.activeTimeouts.set(v, state.activeTimeouts.get(v).exclude(Set(timeout))) }
//   val res = consumed_timeout_state.system.get(v).fire_timeout_event(timeout)
//   apply_effect(consumed_timeout_state, v, res)

// /// use this in REPL to let a process receive a specific message and take a step
// action act_receive_msg (v: ProcessID, msg: Message) : bool = all {
//   s.msgBuffer.get(v).contains(msg),
//   s' = receive_one_message(s, v, msg)
// }

// action act_receive_some_msg (v: ProcessID) : bool = all {
//   s.msgBuffer.get(v) != Set(),
//   nondet msg = oneOf(s.msgBuffer.get(v))
//   act_receive_msg(v, msg)
// }

// /// use this in REPL to let a process fire a specific timeout and take a step
// action act_timeout (v: ProcessID, timeout: TimeoutEvent) : bool = all {
//   s.activeTimeouts.get(v).contains(timeout),
//   s' = fire_one_timeout_event(s, v, timeout)
// }

// action act_some_timeout (v: ProcessID) : bool = all {
//   s.activeTimeouts.get(v) != Set(),
//   nondet timeout = oneOf(s.activeTimeouts.get(v))
//   act_timeout(v, timeout)
// }

// action step =
//   nondet v = oneOf(processes)
//   any {
//     act_receive_some_msg(v),
//     act_some_timeout(v)
//   }

// //
// // Accelerated semantics (multiple process may receive multiple messages/timeouts in one action)
// //

// /// Returns the new state after each message in the msgs map is delivered to the respective receiver
// pure def apply_acceleration_msgs (state: Environment, msgs: ProcessID -> Set[Message]): Environment =
//   msgs.keys().fold(state, (s, v) => 
//     msgs.get(v).fold(s, (s2, msg) => 
//       receive_one_message(s2, v, msg) 
//     ))

// pure def apply_acceleration_timeout (state: Environment, timeouts: ProcessID -> Set[TimeoutEvent]): Environment =
//   timeouts.keys().fold(state, (s, v) => 
//     timeouts.get(v).fold(s, (s2, timeout) => 
//       fire_one_timeout_event(s2, v, timeout)
//     ))

// // non-deterministically pick a set of processes. For each, non-deterministically pick a set of votes
// // and deliver them to the process in one action.
// action acceleration_msgs = 
//   nondet msgs = processes.map(v => s.msgBuffer.get(v).powerset().exclude(Set(Set())).map(m => (v, m)))
//                 .flatten().powerset().oneOf()
//   val deliver = msgs.setToMap() 
//   s' =  apply_acceleration_msgs(s, deliver)

// action acceleration_timeouts = 
//   nondet timeouts = processes.map(v => s.activeTimeouts.get(v).powerset().exclude(Set(Set())).map(t => (v, t)))
//                 .flatten().powerset().oneOf()
//   val deliver = timeouts.setToMap() 
//   s' =  apply_acceleration_timeout(s, deliver)


// action accelerated_step = any {
//   acceleration_msgs,
//   acceleration_timeouts,
// }  




} 



