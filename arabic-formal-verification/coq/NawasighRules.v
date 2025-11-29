(* ============================================================ *)
(* NawasighRules.v - قواعد النواسخ                              *)
(* Copular Verbs Rules (Kana and Sisters, Inna and Sisters)     *)
(* ============================================================ *)

Require Import Coq.Strings.String.
Require Import ArabicGrammar.ArabicGrammar.

(* ============================================================ *)
(* الجزء الأول: كان وأخواتها                                    *)
(* Part 1: Kana and Sisters                                      *)
(* ============================================================ *)

(* أنواع الأفعال الناسخة - Types of Copular Verbs *)
Inductive KanaSister : Type :=
  | Kana       (* كان *)
  | Asbaha     (* أصبح *)
  | Adha       (* أضحى *)
  | Amsa       (* أمسى *)
  | Bata       (* بات *)
  | Zalla      (* ظلّ *)
  | Sara       (* صار *)
  | Laysa.     (* ليس *)

(* جملة كان وأخواتها *)
Record KanaSentence : Type := mkKanaSentence {
  kana_verb : KanaSister;
  ism_kana : NounPhrase;    (* اسم كان - مرفوع *)
  khabar_kana : NounPhrase  (* خبر كان - منصوب *)
}.

(* التحقق من صحة اسم كان (يجب أن يكون مرفوعاً) *)
Definition is_valid_ism_kana (n : NounPhrase) : Prop :=
  noun_case n = Nominative.

(* التحقق من صحة خبر كان (يجب أن يكون منصوباً) *)
Definition is_valid_khabar_kana (n : NounPhrase) : Prop :=
  noun_case n = Accusative.

(* صحة جملة كان وأخواتها *)
Definition valid_kana_sentence (s : KanaSentence) : Prop :=
  is_valid_ism_kana (ism_kana s) /\ is_valid_khabar_kana (khabar_kana s).

(* نظرية كان وأخواتها *)
Theorem kana_sisters_theorem :
  forall (k : KanaSister) (ism khabar : NounPhrase),
    noun_case ism = Nominative ->
    noun_case khabar = Accusative ->
    valid_kana_sentence (mkKanaSentence k ism khabar).
Proof.
  intros k ism khabar Hism Hkhabar.
  unfold valid_kana_sentence.
  unfold is_valid_ism_kana, is_valid_khabar_kana.
  simpl.
  split; assumption.
Qed.

(* مثال: "كان الجوُّ جميلاً" - The weather was beautiful *)
Example kana_aljaw_jamilan :
  let ism := mkNoun "جو" Nominative Masculine Singular true in
  let khabar := mkNoun "جميل" Accusative Masculine Singular false in
  valid_kana_sentence (mkKanaSentence Kana ism khabar).
Proof.
  unfold valid_kana_sentence.
  unfold is_valid_ism_kana, is_valid_khabar_kana.
  simpl.
  split; reflexivity.
Qed.

(* ============================================================ *)
(* الجزء الثاني: إنّ وأخواتها                                   *)
(* Part 2: Inna and Sisters                                      *)
(* ============================================================ *)

(* أنواع الحروف الناسخة *)
Inductive InnaSister : Type :=
  | Inna      (* إنّ *)
  | Anna      (* أنّ *)
  | Kaanna    (* كأنّ *)
  | Lakinna   (* لكنّ *)
  | Layta     (* ليت *)
  | Laalla.   (* لعلّ *)

(* جملة إنّ وأخواتها *)
Record InnaSentence : Type := mkInnaSentence {
  inna_particle : InnaSister;
  ism_inna : NounPhrase;    (* اسم إنّ - منصوب *)
  khabar_inna : NounPhrase  (* خبر إنّ - مرفوع *)
}.

(* التحقق من صحة اسم إنّ (يجب أن يكون منصوباً) *)
Definition is_valid_ism_inna (n : NounPhrase) : Prop :=
  noun_case n = Accusative.

(* التحقق من صحة خبر إنّ (يجب أن يكون مرفوعاً) *)
Definition is_valid_khabar_inna (n : NounPhrase) : Prop :=
  noun_case n = Nominative.

(* صحة جملة إنّ وأخواتها *)
Definition valid_inna_sentence (s : InnaSentence) : Prop :=
  is_valid_ism_inna (ism_inna s) /\ is_valid_khabar_inna (khabar_inna s).

(* نظرية إنّ وأخواتها *)
Theorem inna_sisters_theorem :
  forall (i : InnaSister) (ism khabar : NounPhrase),
    noun_case ism = Accusative ->
    noun_case khabar = Nominative ->
    valid_inna_sentence (mkInnaSentence i ism khabar).
Proof.
  intros i ism khabar Hism Hkhabar.
  unfold valid_inna_sentence.
  unfold is_valid_ism_inna, is_valid_khabar_inna.
  simpl.
  split; assumption.
Qed.

(* مثال: "إنّ العلمَ نورٌ" - Indeed, knowledge is light *)
Example inna_alilm_nour :
  let ism := mkNoun "علم" Accusative Masculine Singular true in
  let khabar := mkNoun "نور" Nominative Masculine Singular false in
  valid_inna_sentence (mkInnaSentence Inna ism khabar).
Proof.
  unfold valid_inna_sentence.
  unfold is_valid_ism_inna, is_valid_khabar_inna.
  simpl.
  split; reflexivity.
Qed.

(* ============================================================ *)
(* نهاية الملف - End of File                                    *)
(* ============================================================ *)
