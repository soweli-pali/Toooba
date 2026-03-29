
// Copyright (c) 2017 Massachusetts Institute of Technology
// 
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

// Alternate free list design:
// The FreeList has the same number of slots as #PhyReg - #ArchReg. When the
// ROB is empty, the FreeList is full. When the ROB is full, the FreeList is
// empty. The FreeList deq method takes the old name for the renamed register
// and writes it to the location just dequeued. On step-by-step rollback, the
// old name is taken from the FreeList and moved back to the RenamingTable.

import Vector::*;
import GetPut::*;
import List::*;
import RevertingVirtualReg::*;
import Types::*;
import ProcTypes::*;
import HasSpecBits::*;
import Ehr::*;

typedef struct {
    PhyRegs phy_regs;
} RenameResult deriving(Bits, Eq, FShow);

interface RTRename;
    // This will rename the architectural registers in r to physical registers.
    // XXX This will **ALWAYS** claim a new physical register as a speculative
    // in-flight renaming, no matter whether the dst reg is valid or not.
    // This simplifies the implementation for superscalar renaming
    method RenameResult getRename(ArchRegs r);
    method Action claimRename(ArchRegs r, SpecBits sb);
    method Bool canRename; // guard of rename
endinterface

interface RTCommit;
    // Commits the oldest instructions. This will free the previous physical
    // register used to hold the value for the architectural destination
    // register.
    method Action commit;
    method Bool canCommit; // guard of commit
endinterface

interface RTMove;
    // Interface to claim move from src to dst register
    method RenameResult getMoveResult(Move m, ArchRegs r);
    method Action claimMove(Move m, SpecBits sb);
    method Bool canMove; // guard of move
endinterface

interface RegRenamingTable;
    interface Vector#(SupSize, RTRename) rename; // rename port
    interface Vector#(SupSize, RTCommit) commit; // commit port
    interface Vector#(SupSize, RTMove) move; // move port

    // This subinterface contains the methods specifying correct and incorrect
    // speculation. If the speculation is correct, the dependencies on that
    // SpecTag should be removed from all SpecBits. If the speculation is
    // incorrect, then all renamings that depended on the SpecTag should be
    // reverted.
    interface SpeculationUpdate specUpdate;
    // methods: method Action incorrectSpeculation(SpecTag tag);
    //          method Action correctSpeculation(SpecTag tag);
endinterface

// actions when we claim a new phy reg in rename
// when isMove phy will be the phy reg after aliassing
// this will not match what we store in the in-flight
// or committed renaming table registers, which is pre-alias
typedef struct {
    Maybe#(ArchRIndx) arch;
    PhyRIndx phy;
    SpecBits specBits;
    Bool isMove;
} RenameClaim deriving(Bits, Eq, FShow);

// actions in case of wrongSpec
typedef struct {
    Bool killAll;
    SpecTag specTag;
} RTWrongSpec deriving(Bits, Eq, FShow);

// entries in the move alias table
typedef struct {
    PhyRIndx dst;
    PhyRIndx src;
} MoveAlias deriving(Bits, Eq, FShow);

typedef struct {
    MoveAlias move;
    locationT dstLocation;
} MoveClaim#(type locationT) deriving(Bits, Eq, FShow);

typedef struct {
    moveIndexT moveTableIndex;
    locationT newLocation;
} MoveUpdate#(type moveIndexT, type locationT) deriving(Bits, Eq, FShow);

typedef union tagged {
    rtIndexT RtIndx;
    indexT InFlightIndx;
} LocationT#(type rtIndexT, type indexT) deriving(Bits, Eq, FShow);

(* synthesize *)
module mkRegRenamingTable(RegRenamingTable) provisos (
    NumAlias#(size, TSub#(NumPhyReg, NumArchReg)),
    NumAlias#(moveTableSize, 3),
    Alias#(moveCountT, Bit#(TLog#(TAdd#(moveTableSize, 1)))),
    Alias#(moveIndexT, Bit#(TLog#(moveTableSize))),
    Alias#(indexT, Bit#(TLog#(size))),
    Alias#(rtIndexT, Bit#(TLog#(NumArchReg))),
    Alias#(locationT, LocationT#(rtIndexT, indexT)),
    Alias#(moveClaim, MoveClaim#(locationT)),
    Alias#(moveUpdate, MoveUpdate#(moveIndexT, locationT)),
    Alias#(vTagT, Bit#(TLog#(TMul#(2, size)))) // virtual tag: 0 -- size*2-1
);
    // ordering: commit < rename < correctSpec
    // commit < wrongSpec
    // wrongSpec C rename
    
    // NOTES:
    // rename do not need to see the effect of commit
    // rename is conflict with wrongSpec, so don't need to see its effect
    // The real actions of commit, wrongSpec and rename will be done in canon rule

    // rename is split into two parts in EHR port assignment:
    // - get (get the phy reg for src and dst arch regs, in rename method)
    // - claim (truly claim a free phy reg for dst arch reg, in canon rule)

    // Although the EHR ports of commit should also be split into two parts,
    // we don't need to do so, because the method of commit is directly followed by canon rule.

    // EHR ports for renaming_table
    Integer rt_get_port = 0;
    function Integer rt_commit_port(Integer i) = i;
    Integer rt_replace_port = valueof(SupSize);

    // EHR ports for valid
    Integer valid_get_port = 0;
    Integer valid_commit_port = 0;
    Integer valid_wrongSpec_port = 1;
    Integer valid_claim_port = 1;

    // EHR ports for new_renamings_phy
    Integer nrp_get_port = 0;
    Integer nrp_commit_port = 0;
    Integer nrp_replace_port = 1;

    // EHR ports for spec_bits
    Integer sb_wrongSpec_port = 0;
    Integer sb_claim_port = 0;
    Integer sb_correctSpec_port = 1;

    // non-speculative renaming table at commit port
    // initially arch reg i --> phy reg i
    Vector#(NumArchReg, Ehr#(TAdd#(SupSize, 1), PhyRIndx)) renaming_table <- genWithM(compose(mkEhr, fromInteger));

    // A FIFO of
    // - in-flight renaming: when valid = True i.e. within [enqP, deqP)
    // - free phy reg: when valid = False i.e. outside [enqP, deqP)
    // We store the arch reg and phy reg separately to reduce EHR ports
    // XXX A valid in-flight renaming may have arch reg being invalid
    // This happens in case we claim a phy reg while the dst arch reg is invalid
    Vector#(size, Reg#(Maybe#(ArchRIndx))) new_renamings_arch <- replicateM(mkRegU);
    function m#(Ehr#(2, PhyRIndx)) genNewRenamingsPhy(Integer i) provisos (IsModule#(m, a__));
        return mkEhr(fromInteger(i + valueOf(NumArchReg))); // free phy regs initially
    endfunction
    Vector#(size, Ehr#(2, PhyRIndx)) new_renamings_phy <- genWithM(genNewRenamingsPhy);
    Vector#(size, Ehr#(2, Bool)) valid <- replicateM(mkEhr(False));
    Vector#(size, Ehr#(2, SpecBits)) spec_bits <- replicateM(mkEhr(0));
    Reg#(indexT) enqP <- mkReg(0); // point to claim free phy reg
    Reg#(indexT) deqP <- mkReg(0); // point to commit renaming and make phy reg free

    // wires/EHRs to record actions
    Vector#(SupSize, RWire#(RenameClaim)) claimEn <- replicateM(mkUnsafeRWire);
    Vector#(SupSize, PulseWire) commitEn <- replicateM(mkPulseWire);
    RWire#(RTWrongSpec) wrongSpecEn <- mkRWire;

    // ordering regs
    Vector#(SupSize, Reg#(Bool)) commit_SB_rename <- replicateM(mkRevertingVirtualReg(True));
    Reg#(Bool) commit_SB_wrongSpec <- mkRevertingVirtualReg(True);

    // wrong spec conflict with rename
    Vector#(SupSize, RWire#(void)) wrongSpec_rename_conflict <- replicateM(mkRWire);

    // move table
    // store dst in renaming table and in-flight fifo as normal
    // when query would otherwise return PhyRIndx dst, instead return src
    // if we free src instead:
    // 1. replace dst with src wherever it previously occured
    // 2. free dst
    // and whenever we free dst (including above) we remove move table entry
    // dst may only appear in the table once
    // src can appear multiple times
    // ehr ports above 0 only used for writes
    Vector#(moveTableSize, Reg#(MoveAlias)) move_table <- replicateM(mkRegU);
    Vector#(moveTableSize, Reg#(locationT)) move_dst_locations <- replicateM(mkRegU);
    Vector#(moveTableSize, Reg#(Bool)) move_valid <- replicateM(mkReg(False));

    Vector#(SupSize, RWire#(moveIndexT)) freeMoveEn <- replicateM(mkUnsafeRWire);
    Vector#(SupSize, RWire#(moveClaim)) allocateMoveEn <- replicateM(mkUnsafeRWire);
    Vector#(SupSize, RWire#(moveUpdate)) dstLocationUpdateEn <- replicateM(mkUnsafeRWire);
    // replace enqueued when src would otherwise be freed
    Vector#(SupSize, RWire#(moveClaim)) phyReplaceEn <- replicateM(mkUnsafeRWire);

    function PhyRIndx applyPriorReplacements(PhyRIndx phy, Integer idx);
        PhyRIndx result = phy;
        for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
            if(idx > i) begin 
                if(phyReplaceEn[i].wget() matches tagged Valid .mc) begin 
                    if(mc.move.dst == phy) begin 
                        result = mc.move.src;
                    end
                end
            end
        end
        return result;
    endfunction

    Ehr#(TAdd#(SupSize, 1), moveCountT) free_move_slots <- mkEhr(fromInteger(valueof(moveTableSize)));

    (* fire_when_enabled, no_implicit_conditions *)
    rule allocate_to_move_table;
        // apply allocations
        // assume allocations are already flattened
        Vector#(moveTableSize, Bool) allocated = replicate(False);
        for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
            if(allocateMoveEn[i].wget() matches tagged Valid .mc) begin 
                Bool allocation_done = False;
                for(Integer j = 0; j < valueof(moveTableSize); j = j+1) begin
                    if(!allocation_done && !move_valid[j] && !allocated[j]) begin 
                        move_table[j] <= mc.move;
                        move_dst_locations[j] <= mc.dstLocation;
                        move_valid[j] <= True;
                        allocated[j] = True;
                        allocation_done = True;
                    end
                end
                // sanity check
                doAssert(allocation_done, "All scheduled allocations must have a slot available");
            end
        end
    endrule

        (* fire_when_enabled, no_implicit_conditions *)
    rule free_from_move_table;
        // apply frees
        Vector#(moveTableSize, Bool) freed = replicate(False);
        for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
            if(freeMoveEn[i].wget() matches tagged Valid .idx) begin 
                // sanity checks
                doAssert(!freed[idx], "Must not free the same move table index twice in the same cycle");
                doAssert(move_valid[idx], "Freed move index must be valid");
                if(!freed[idx] && move_valid[idx]) begin 
                    move_valid[idx] <= False;
                    freed[idx] = True;
                end
            end
        end
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule apply_replacements;
        Vector#(size, Bool) inFlightReplaced = replicate(False);
        Vector#(NumArchReg, Bool) rtReplaced = replicate(False);
        for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
            if(phyReplaceEn[i].wget() matches tagged Valid .mc) begin 
                case(mc.dstLocation) matches 
                    tagged RtIndx .idx: begin 
                        // sanity check
                        doAssert(!rtReplaced[idx], "Move substitution must not replace the same location in rename table twice in one cycle");
                        if(!rtReplaced[idx]) begin 
                            renamingTable[idx][rt_replace_port] <= mc.move.src;
                            rtReplaced[idx] = True;
                        end
                    end 
                    tagged InFlightIndx .idx: begin 
                        // sanity check
                        doAssert(!inFlightReplaced[idx], "Move substitution must not replace the same location in in flight renaming table twice in one cycle");
                        if(!inFlightReplaced[idx]) begin 
                            new_renamings_phy[idx][nrp_replace_port] <= mc.move.src;
                            inFlightReplaced[idx] = True;
                        end
                    end
                endcase
            end
        end
    endrule

    (* fire_when_enabled, no_implicit_conditions *)
    rule update_dst_locations;
        Vector#(moveTableSize, Bool) updated = replicate(False);
        for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
            if(dstLocationUpdateEn[i].wget() matches tagged Valid .lu) begin 
                // sanity checks
                moveIndexT idx = lu.moveTableIdx;
                doAssert(move_valid[idx], "Move table index being updated must be valid");
                doAssert(!updated[idx], "Move table dst location must only be updated once");
                if(!updated[idx] && move_valid[idx]) begin 
                    move_dst_locations[idx] <= lu.newLocation;
                    updated[idx] = True;
                end
            end
        end
    endrule

    function Bool isMoveIndexFreed(moveIndexT idx, Integer portIdx);
        Bool result = False;
        for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
            if(i < portIdx) begin 
                if(freeMoveEn[i] matches tagged Valid .freed_idx) begin 
                    result = result || idx == freed_idx;
                end
            end
        end
        return result;
    endfunction 

    function Maybe#(moveIndexT) getMoveIdxBySource(PhyRIndx src, Integer portIdx);
        Maybe#(moveIndexT) result = Invalid;
        Bool result_found = False;
        for(Integer i = 0; i < valueof(moveTableSize); i = i+1) begin
            if(!result_found
                && move_valid[i]
                && !isMoveIndexFreed(fromInteger(i), portIdx)
                && move_table[i].src == src
            ) begin 
                result = Valid (fromInteger(i));
                result_found = True;
            end
        end
        return result;
    endfunction

    function Maybe#(moveIndexT) getMoveIdxByDst(PhyRIndx dst, Integer portIdx);
        Maybe#(moveIndexT) result = Invalid;
        Bool result_found = False;
        for(Integer i = 0; i < valueof(moveTableSize); i = i+1) begin
            if(!result_found
                && move_valid[i]
                && !isMoveIndexFreed(fromInteger(i), portIdx)
                && move_table[i].dst == dst
            ) begin 
                result = Valid (fromInteger(i));
                result_found = True;
            end
        end
        return result;
    endfunction

    // functions for querying and modifying move table *always* read state at start of cycle
    // the only exception is the move_freed wires
    // these are used in 
    function Maybe#(PhyRIndx) getMoveSource(PhyRIndx dst);
        Maybe#(PhyRIndx) result = Invalid;
        for(Integer i = 0; i < valueof(moveTableSize); i = i+1) begin
            if(move_valid[i][mt_read_port] && move_table[i][mt_read_port].dst == dst) begin 
                result = Valid (move_table[i].src);
            end
        end
        return result;
    endfunction

    function indexT getNextIndex(indexT idx);
        return idx == fromInteger(valueof(size) - 1) ? 0 : idx + 1;
    endfunction

    function indexT incrIndex(indexT idx, SupCnt incr);
        Bit#(TLog#(TAdd#(size, 1))) newIdx = zeroExtend(idx) + zeroExtend(incr);
        if(newIdx >= fromInteger(valueof(size))) begin
            newIdx = newIdx - fromInteger(valueof(size));
        end
        return truncate(newIdx);
    endfunction

    // get the index to query renaming_table
    function rtIndxT getRTIndex(ArchRIndx arch) = pack(arch);

    // vector of index to claim free phy regs for each rename port
    Vector#(SupSize, indexT) claimIndex;
    for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
        claimIndex[i] = incrIndex(enqP, fromInteger(i));
    end

    // vector of index to commit phy regs for each commit port
    Vector#(SupSize, indexT) commitIndex;
    for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
        commitIndex[i] = incrIndex(deqP, fromInteger(i));
    end

    // similar to LSQ, get virtual tag by using enqP as pivot (enqP is changed at end of cycle)
    // valid entry i --> i < enqP ? i + size : i
    // NOTE that virtual tag only works for **valid** entry
    function vTagT getVTag(indexT i);
        return i < enqP ? zeroExtend(i) + fromInteger(valueof(size)) : zeroExtend(i);
    endfunction
    Vector#(size, vTagT) vTags = map(getVTag, genWith(fromInteger));

    // find oldest entry using virtual tag (i.e. smallest)
    function Maybe#(indexT) findOldest(Vector#(size, Bool) pred);
        function indexT getOlder(indexT a, indexT b);
            if(!pred[a]) begin
                return b;
            end
            else if(!pred[b]) begin
                return a;
            end
            else begin
                return vTags[a] < vTags[b] ? a : b;
            end
        endfunction
        Vector#(size, indexT) idxVec = genWith(fromInteger);
        indexT tag = fold(getOlder, idxVec);
        return pred[tag] ? Valid (tag) : Invalid;
    endfunction

    // find youngest entry using virtual tag (i.e. largest)
    function Maybe#(indexT) findYoungest(Vector#(size, Bool) pred);
        function indexT getOlder(indexT a, indexT b);
            if(!pred[a]) begin
                return b;
            end
            else if(!pred[b]) begin
                return a;
            end
            else begin
                return vTags[a] < vTags[b] ? b : a;
            end
        endfunction
        Vector#(size, indexT) idxVec = genWith(fromInteger);
        indexT tag = fold(getOlder, idxVec);
        return pred[tag] ? Valid (tag) : Invalid;
    endfunction

    // canonicalize deq, wrongSpec/enq
    (* fire_when_enabled, no_implicit_conditions *)
    rule canon;
        Vector#(SupSize, SupWaySel) supIdxVec = genWith(fromInteger);

        // apply commit actions
        for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
            if(commitEn[i]) begin
                indexT curDeqP = commitIndex[i]; // deqP for new renamings
                PhyRIndx commit_phy_reg = new_renamings_phy[curDeqP][nrp_commit_port];
                Maybe#(ArchRIndx) commit_arch_reg = new_renamings_arch[curDeqP];
                if(commit_arch_reg matches tagged Valid .arch) begin
                    let rtIdx = getRTIndex(arch);
                    // free phy reg being overwritten in the renaming_table (arch reg is don't care)
                    PhyRIndx freed_phy_reg = renaming_table[rtIdx][rt_commit_port(i)];
                    // apply prior replacements
                    freed_phy_reg = applyPriorReplacements(freed_phy_reg, i);
                    // if freed_phy_reg is src then instead free dst
                    if(getMoveIdxBySource(freed_phy_reg, i) matches tagged Valid .idx) begin 
                        MoveAlias move = move_table[i];
                        freed_phy_reg = move.dst;
                        // replace prior occurance of dst with src
                        phyReplaceEn[i].wset(MoveClaim {
                            move: move 
                            dstLocation: move_dst_locations[i]});
                        // free move table entry
                        freeMoveEn[i].wset(idx);
                    end
                    // free phy reg
                    new_renamings_phy[curDeqP][nrp_commit_port] <= freed_phy_reg;
                    valid[curDeqP][valid_commit_port] <= False;
                    // update renaming_table
                    renaming_table[rtIdx][rt_commit_port(i)] <= commit_phy_reg;
                    // update dstLocation
                    if(getMoveIdxByDst(commit_phy_reg, i) matches tagged Valid .idx) begin 
                        dstLocationUpdateEn[i].wset(MoveUpdate {
                            moveTableIndex: idx,
                            newLocation: tagged RtIndx rtIdx
                        });
                    end
                    // if dst freed then free move table entry
                    if(getMoveIdxByDst(freed_phy_reg, i) matches tagged Valid .idx) begin 
                        freeMoveEn[i].wset(idx);
                    end
                end
                else begin
                    // free the phy reg claimed by this renaming (arch reg is don't care)
                    valid[curDeqP][valid_commit_port] <= False;
                end
                // sanity check
                doAssert(valid[curDeqP][valid_commit_port], "committing entry must be valid");
            end
        end
        // move deqP: find the first non-commit port
        function Bool notCommit(SupWaySel i) = !commitEn[i];
        indexT nextDeqP;
        if(find(notCommit, supIdxVec) matches tagged Valid .idx) begin
            nextDeqP = commitIndex[idx];
            // sanity check: commit is done consecutively
            for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
                doAssert((fromInteger(i) < idx) == commitEn[i], "commit must be consecutive");
            end
        end
        else begin
            nextDeqP = incrIndex(deqP, fromInteger(valueof(SupSize)));
        end
        deqP <= nextDeqP;

        // do wrongSpec OR claim free phy reg
        if(wrongSpecEn.wget matches tagged Valid .x) begin
            Bool killAll = x.killAll;
            SpecTag specTag = x.specTag;
            Vector#(size, indexT) idxVec = genWith(fromInteger);
            // do wrongSpec, first kill entries (make in-flight renaming to free phy reg)
            function Bool needKill(indexT i);
                return killAll || spec_bits[i][sb_wrongSpec_port][specTag] == 1;
            endfunction
            Vector#(size, Bool) isKill = map(needKill, idxVec);
            function Action kill(indexT i);
            action
                if(isKill[i]) begin
                    valid[i][valid_wrongSpec_port] <= False;
                end
            endaction
            endfunction
            joinActions(map(kill, idxVec));
            // move enqP: find the oldest **valid** entry being killed
            Vector#(size, Bool) killValid = zipWith( \&& , isKill , readVEhr(valid_wrongSpec_port, valid) );
            indexT nextEnqP = enqP;
            if(findOldest(killValid) matches tagged Valid .idx) begin
                nextEnqP = idx;
            end
            enqP <= nextEnqP;
        end
        else begin
            // claim phy reg
            for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
                if(claimEn[i].wget matches tagged Valid .claim) begin
                    indexT curEnqP = claimIndex[i];
                    new_renamings_arch[curEnqP] <= claim.arch; // keep phy reg unchanged
                    valid[curEnqP][valid_claim_port] <= True;
                    spec_bits[curEnqP][sb_claim_port] <= claim.specBits;
                    if(claim.isMove) begin 
                        allocateMoveEn[i].wset(MoveClaim {
                            move: MoveAlias {
                                dst: new_renamings_phy[curEnqP][nrp_get_port],
                                src: claim.phy
                            },
                            dstLocation: tagged InFlightIndx curEnqP
                        });
                    end
                    // sanity check
                    doAssert(!valid[curEnqP][valid_get_port], "claiming entry must be invalid");
                    doAssert(claim.isMove || claim.phy == new_renamings_phy[curEnqP][nrp_get_port], "phy reg should match if not move");
                    doAssert(!claim.isMove || claim.phy != new_renamings_phy[curEnqP][nrp_get_port], "phy reg should not match if move");
                end
            end
            // move enqP: find the first non-claim port
            function Bool notClaim(SupWaySel i) = !isValid(claimEn[i].wget);
            indexT nextEnqP;
            if(find(notClaim, supIdxVec) matches tagged Valid .idx) begin
                nextEnqP = claimIndex[idx];
                // sanity check: rename is consecutive
                for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
                    doAssert((fromInteger(i) < idx) == isValid(claimEn[i].wget), "claim is consecutive");
                end
            end
            else begin
                nextEnqP = incrIndex(enqP, fromInteger(valueof(SupSize)));
            end
            enqP <= nextEnqP;
        end
    endrule

`ifdef BSIM
    // sanity check in simulation
    // all valid entry are within [deqP, enqP), outsiders are invalid entries
    (* fire_when_enabled, no_implicit_conditions *)
    rule sanityCheck;
        Bool empty = all( \== (False), readVEhr(0, valid) );
        function Bool in_range(indexT i);
            // i is within [deqP, enqP)
            if(empty) begin
                return False;
            end
            else begin
                if(deqP < enqP) begin
                    return deqP <= i && i < enqP;
                end
                else begin
                    return deqP <= i || i < enqP;
                end
            end
        endfunction
        for(Integer i = 0; i < valueof(size); i = i+1) begin
            doAssert(in_range(fromInteger(i)) == valid[i][0],
                "entries inside [deqP, enqP) should be valid, otherwise invalid"
            );
        end
        doAssert(enqP <= fromInteger(valueof(size) - 1), "enqP < size");
        doAssert(deqP <= fromInteger(valueof(size) - 1), "deqP < size");
    endrule
`endif


    // function to search claimed phy regs just in this cycle to
    // get phy reg for an arch reg for get_renaming at port getPort
    function Maybe#(PhyRIndx) search_claimed_renamings(Integer getPort, ArchRIndx arch_reg);
        List#(RWire#(RenameClaim)) claims = List::take(getPort, toList(claimEn));
        function Maybe#(PhyRIndx) getHit(RWire#(RenameClaim) clm);
            if(clm.wget matches tagged Valid .e) begin
                return e.arch == (Valid (arch_reg)) ? Valid (e.phy) : Invalid;
            end
            else begin
                return Invalid;
            end
        endfunction
        List#(Maybe#(PhyRIndx)) hitList = List::map(getHit, claims);
        // find the most recently claimed phy reg (i.e. largest list index)
        Maybe#(Maybe#(PhyRIndx)) hit = List::find(isValid, List::reverse(hitList));
        return fromMaybe(Invalid, hit);
    endfunction

    // function to search new_renamings to get phy reg for an arch reg
    function Maybe#(PhyRIndx) search_new_src_renamings(ArchRIndx arch_reg);
        // first get all hitting in-flight renamings
        function Bool hit(Integer i);
            return valid[i][valid_get_port] && new_renamings_arch[i] == (Valid (arch_reg));
        endfunction
        Vector#(size, Bool) isHit = map(hit, genVector);
        // find the youngest
        if(findYoungest(isHit) matches tagged Valid .idx) begin
            return Valid (new_renamings_phy[idx][nrp_get_port]);
        end
        else begin
            return Invalid;
        end
    endfunction

    // function to get phy reg for an arch reg for get_renaming at port getPort
    // priority: newly claimed -> new_renamings -> renaming_table
    function PhyRIndx get_src_renaming(Integer getPort, ArchRIndx arch_reg);
        let claim_phy_reg = search_claimed_renamings(getPort, arch_reg);
        let new_phy_reg = search_new_src_renamings(arch_reg);
        let existing_phy_reg = renaming_table[getRTIndex(arch_reg)][rt_get_port];
        PhyRIndx result = fromMaybe(fromMaybe(existing_phy_reg, new_phy_reg), claim_phy_reg);
        return fromMaybe(result, getMoveSource(result));
    endfunction

    // function to find a free phy reg to claim (at port claimPort) for a dst arch reg
    function PhyRIndx get_dst_renaming(Integer claimPort);
        return new_renamings_phy[claimIndex[claimPort]][nrp_get_port];
    endfunction

    function Bool isFpuReg(ArchRIndx arch_reg);
        return arch_reg matches tagged Fpu .* ? True : False;
    endfunction

    Vector#(SupSize, RTRename) renameIfc;
    for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
        // XXX we always claim a free phy reg, but only return it if arch dst reg is valid
        Bool guard = !valid[claimIndex[i]][valid_get_port];
        PhyRIndx claim_phy_reg = get_dst_renaming(i);
        renameIfc[i] = (interface RTRename;
            method RenameResult getRename(ArchRegs r) if(guard);
                // get renamings
                PhyRegs phy_regs = PhyRegs {
                    src1: tagged Invalid,
                    src2: tagged Invalid,
                    src3: tagged Invalid,
                    dst: tagged Invalid
                };
                if (r.src1 matches tagged Valid .valid_src1) begin
                    phy_regs.src1 = Valid (get_src_renaming(i, valid_src1));
                end
                if (r.src2 matches tagged Valid .valid_src2) begin
                    phy_regs.src2 = Valid (get_src_renaming(i, valid_src2));
                end
                if (r.src3 matches tagged Valid .valid_src3) begin
                    phy_regs.src3 = tagged Valid (get_src_renaming(i, tagged Fpu valid_src3));
                end
                if (r.dst matches tagged Valid .valid_dst) begin
                    phy_regs.dst = Valid (PhyDst {
                        indx: claim_phy_reg,
                        isFpuReg: isFpuReg(valid_dst)
                    });
                end

                return RenameResult {
                    phy_regs: phy_regs
                };
            endmethod

            method Action claimRename(ArchRegs r, SpecBits sb) if(guard);
                // record the claim
                claimEn[i].wset(RenameClaim {
                    arch: r.dst,
                    phy: claim_phy_reg,
                    specBits: sb
                });
                // conflict with wrong spec
                wrongSpec_rename_conflict[i].wset(?);
                // ordering with commit
                commit_SB_rename[i] <= False;
            endmethod
            
            method canRename = guard;
        endinterface);
    end

    Vector#(SupSize, RTMove) moveIfc;
    for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
        Bool guard = !valid[claimIndex[i]][valid_get_port] && free_move_slots[i] > 0;
        moveIfc[i] = (interface RTMove;
            method RenameResult getMoveResult(Move m, ArchRegs r) if(guard);
                // get renamings
                PhyRegs phy_regs = PhyRegs {
                    src1: tagged Invalid,
                    src2: tagged Invalid,
                    src3: tagged Invalid,
                    dst: tagged Invalid
                };
                if (r.src1 matches tagged Valid .valid_src1) begin
                    phy_regs.src1 = Valid (get_src_renaming(i, valid_src1));
                end
                if (r.src2 matches tagged Valid .valid_src2) begin
                    phy_regs.src2 = Valid (get_src_renaming(i, valid_src2));
                end
                if (r.src3 matches tagged Valid .valid_src3) begin
                    phy_regs.src3 = tagged Valid (get_src_renaming(i, tagged Fpu valid_src3));
                end
                if (r.dst matches tagged Valid .valid_dst) begin
                    phy_regs.dst = Valid (PhyDst {
                        indx: get_src_renaming(i, m.src),
                        isFpuReg: isFpuReg(valid_dst)
                    });
                end

                return RenameResult {
                    phy_regs: phy_regs
                };
            endmethod

            method Action claimMove(Move m, SpecBits sb) if(guard);
                // deduct move slot
                free_move_slots[i] <= free_move_slots[i] - 1;
                // record the claim
                claimEn[i].wset(RenameClaim {
                    arch: tagged Valid m.dst,
                    phy: get_src_renaming(i, m.src),
                    specBits: sb,
                    isMove: True
                });
                // conflict with wrong spec
                wrongSpec_rename_conflict[i].wset(?);
                // ordering with commit
                commit_SB_rename[i] <= False;
            endmethod

            method canMove = guard;
        endinterface);
    end

    Vector#(SupSize, RTCommit) commitIfc;
    for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
        Bool guard = valid[commitIndex[i]][valid_commit_port] &&
                     all(id, readVReg(commit_SB_rename)) && // ordering: commit < rename
                     commit_SB_wrongSpec; // ordering: commit < wrongSpec
        commitIfc[i] = (interface RTCommit;
            method Action commit if(guard);
                commitEn[i].send; // record commit action
            endmethod
            method canCommit = guard;
        endinterface);
    end

    interface rename = renameIfc;
    interface commit = commitIfc;
    interface move = moveIfc;

    interface SpeculationUpdate specUpdate;
        method Action incorrectSpeculation(Bool killAll, SpecTag specTag);
            // record wrongSpec
            wrongSpecEn.wset(RTWrongSpec {
                killAll: killAll,
                specTag: specTag
            });
            // conflict with rename
            for(Integer i = 0; i < valueof(SupSize); i = i+1) begin
                wrongSpec_rename_conflict[i].wset(?);
            end
            // order after commit
            commit_SB_wrongSpec <= False;
        endmethod
        method Action correctSpeculation(SpecBits mask);
            function Action correctSpec(Integer i);
            action
                spec_bits[i][sb_correctSpec_port] <= spec_bits[i][sb_correctSpec_port] & mask;
            endaction
            endfunction
            Vector#(size, Integer) idxVec = genVector;
            joinActions(map(correctSpec, idxVec));
        endmethod
    endinterface
endmodule
