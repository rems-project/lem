(**************************************************************************)
(*     ARM/Power Multiprocessor Machine Code Semantics: HOL sources       *)
(*                                                                        *)
(*                                                                        *)
(*  Jade Alglave (2), Anthony Fox (1), Samin Isthiaq (3),                 *)
(*  Magnus Myreen (1), Susmit Sarkar (1), Peter Sewell (1),               *)
(*  Francesco Zappa Nardelli (2)                                          *)
(*                                                                        *)
(*   (1) Computer Laboratory, University of Cambridge                     *)
(*   (2) Moscova project, INRIA Paris-Rocquencourt                        *)
(*   (3) Microsoft Research Cambridge                                     *)
(*                                                                        *)
(*     Copyright 2007-2008                                                *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*                                                                        *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*     products derived from this software without specific prior         *)
(*     written permission.                                                *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,          *)
(*  WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING             *)
(*  NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS    *)
(*  SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.          *)
(*                                                                        *)
(**************************************************************************)

signature HolDoc = sig

(*

  Code to automatically generate .imn information for theories at
  export time.  Output is in file <thyname>.imn.

  To get this to work it must be the last module opened (more
  accurately, it must override bossLib and HolKernel, and so must
  follow these two).

*)

  include Abbrev
  val export_theory : unit -> unit
  val Define : term quotation -> thm
  val xDefine : string -> term quotation -> thm

end;
