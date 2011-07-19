(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2001-2003                                               *)
(*   George C. Necula    <necula@cs.berkeley.edu>                         *)
(*   Scott McPeak        <smcpeak@cs.berkeley.edu>                        *)
(*   Wes Weimer          <weimer@cs.berkeley.edu>                         *)
(*   Ben Liblit          <liblit@cs.berkeley.edu>                         *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*                                                                        *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*                                                                        *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*                                                                        *)
(*  3. The names of the contributors may not be used to endorse or        *)
(*  promote products derived from this software without specific prior    *)
(*  written permission.                                                   *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS   *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT     *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS     *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE        *)
(*  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,   *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,  *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;      *)
(*  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER      *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT    *)
(*  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN     *)
(*  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE       *)
(*  POSSIBILITY OF SUCH DAMAGE.                                           *)
(*                                                                        *)
(*  File modified by CEA (Commissariat � l'�nergie atomique et aux        *)
(*                        �nergies alternatives).                         *)
(**************************************************************************)

val nextident : int ref

(* the three functions below should be replaced by direct calls to
   Parameters.ContinueOnAnnotError but there are still dependencies issues. *)

val continue_annot_error_set: unit -> unit
val continue_annot_error_unset: unit -> unit

(** Try do do the job. If exception and continue on error is set, catch it and to
    the fallback with proper warning. 
    
    Usage: [continue_annot job backtrack "Ignoring foo"]
*)
val continue_annot : Cabs.cabsloc -> 
  (unit -> 'a) -> (unit -> 'a) -> 
  ('b,Format.formatter,unit,'a) format4 -> 'b

val getident : unit -> int
val currentLoc : unit -> Cabs.cabsloc
val cabslu : Cabs.cabsloc
val commentsGA : (Cabs.cabsloc * string * bool) GrowArray.t
val missingFieldDecl : string * Cabs.decl_type * 'a list * Cabs.cabsloc
val isStatic : Cabs.spec_elem list -> bool
val isExtern : Cabs.spec_elem list -> bool
val isInline : Cabs.spec_elem list -> bool
val isTypedef : Cabs.spec_elem list -> bool
val get_definitionloc : Cabs.definition -> Cabs.cabsloc
val get_statementloc : Cabs.statement -> Cabs.cabsloc
val explodeStringToInts : string -> int64 list
val valueOfDigit : char -> int64
val d_cabsloc : Cabs.cabsloc Pretty_utils.formatter
