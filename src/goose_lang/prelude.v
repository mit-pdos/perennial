(* Gooselang dependencies included in every translated Goose file. *)
From Perennial.goose_lang Require Export base_prelude.
(* Gooselang dependencies that are generated from features modeled as Goose 
   compatible Go code, such as the channel model, which is implemented as 
   a Go generic struct. *)
From Goose.github_com.goose_lang.goose
Require Export channel
.