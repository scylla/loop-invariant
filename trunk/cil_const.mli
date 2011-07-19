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

(** smart constructors for some data types *)
open Cil_types

val voidType: typ

(** forward reference to current location (see {!Cil.CurrentLoc})*)
module CurrentLoc: State_builder.Ref with type data = location

(** Pretty-print a location *)
val d_loc: Format.formatter -> location -> unit

(** Pretty-print the [(CurrentLoc.get ())] *)
val d_thisloc: Format.formatter -> unit

(** Localized user-error with exception raised. *)
val error: ('a, Format.formatter, unit, 'b) format4 -> 'a
(** Localized internal-error with exception raised. *)
val fatal: ('a, Format.formatter, unit, 'b) format4 -> 'a

(** creates a new counter that is project-aware.
    TODO: internalize this module and put all its instances from Cil to here.
*)
module Build_Counter(Name:sig val name:string end) : sig
  val next: unit -> int
  val reset: unit -> unit
  val get: unit -> int
  val self: State.t
end

module Vid: sig
  val next: unit -> int
  val reset: unit -> unit
  val get: unit -> int
  val self: State.t
end


(** set the vid to a fresh number. *)
val set_vid: varinfo -> unit

(** returns a copy of the varinfo with a fresh vid. *)
val copy_with_new_vid: varinfo -> varinfo

val new_raw_id: unit -> int
  (** Generate a new ID. This will be different than any variable ID
      that is generated by {!Cil.makeLocalVar} and friends.
      Must not be used for setting vid: use {!set_vid} instead. *)


(** Create a fresh logical variable giving its name and type. *)
val make_logic_var : string -> logic_type -> logic_var

(** Create a fresh logical variable giving its name and type. *)
val make_logic_info : string -> (* logic_type -> *) logic_info

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
