(* ============================================================ *)
(* ArabicGrammar.v - التحقق الرسمي من القواعد النحوية العربية    *)
(* Arabic Grammar Formal Verification using COQ                  *)
(* Part of SFGCOQ - Systemic Functional Grammar COQ Project     *)
(* ============================================================ *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* ============================================================ *)
(* الجزء الأول: تعريف الأنواع الأساسية                           *)
(* Part 1: Basic Type Definitions                                *)
(* ============================================================ *)

(* حالات الإعراب - Grammatical Cases *)
Inductive Case : Type :=
  | Nominative   (* الرفع - marfou *)
  | Accusative   (* النصب - mansoub *)
  | Genitive.    (* الجر - majrour *)

(* الجنس النحوي - Grammatical Gender *)
Inductive Gender : Type :=
  | Masculine    (* مذكر *)
  | Feminine.    (* مؤنث *)

(* العدد النحوي - Grammatical Number *)
Inductive Number : Type :=
  | Singular     (* مفرد *)
  | Dual         (* مثنى *)
  | Plural.      (* جمع *)

(* أنواع الكلمات - Word Types *)
Inductive WordType : Type :=
  | Noun         (* اسم *)
  | Verb         (* فعل *)
  | Particle.    (* حرف *)

(* زمن الفعل - Verb Tense *)
Inductive VerbTense : Type :=
  | Past         (* ماضي *)
  | Present      (* مضارع *)
  | Imperative.  (* أمر *)

(* ============================================================ *)
(* الجزء الثاني: تعريف مكونات الجملة                            *)
(* Part 2: Sentence Component Definitions                        *)
(* ============================================================ *)

(* الاسم مع خصائصه - Noun with properties *)
Record NounPhrase : Type := mkNoun {
  noun_root : string;
  noun_case : Case;
  noun_gender : Gender;
  noun_number : Number;
  noun_definite : bool  (* معرفة أو نكرة *)
}.

(* الفعل مع خصائصه - Verb with properties *)
Record VerbPhrase : Type := mkVerb {
  verb_root : string;
  verb_tense : VerbTense;
  verb_gender : Gender;
  verb_number : Number
}.

(* ============================================================ *)
(* الجزء الثالث: تعريف أنواع الجمل                              *)
(* Part 3: Sentence Type Definitions                             *)
(* ============================================================ *)

(* الجملة الاسمية - Nominal Sentence: مبتدأ + خبر *)
Record NominalSentence : Type := mkNominal {
  mubtada : NounPhrase;    (* المبتدأ - Subject *)
  khabar : NounPhrase      (* الخبر - Predicate *)
}.

(* الجملة الفعلية - Verbal Sentence: فعل + فاعل *)
Record VerbalSentence : Type := mkVerbal {
  verb : VerbPhrase;       (* الفعل *)
  faail : NounPhrase       (* الفاعل - Subject/Agent *)
}.

(* الجملة الفعلية المتعدية - Transitive Verbal Sentence *)
Record TransitiveSentence : Type := mkTransitive {
  t_verb : VerbPhrase;
  t_faail : NounPhrase;
  mafoul_bih : NounPhrase  (* المفعول به - Object *)
}.

(* ============================================================ *)
(* الجزء الرابع: قواعد التحقق من صحة الإعراب                    *)
(* Part 4: Grammatical Validity Rules                            *)
(* ============================================================ *)

(* التحقق من أن المبتدأ مرفوع *)
Definition is_valid_mubtada (n : NounPhrase) : Prop :=
  noun_case n = Nominative.

(* التحقق من أن الخبر مرفوع *)
Definition is_valid_khabar (n : NounPhrase) : Prop :=
  noun_case n = Nominative.

(* التحقق من أن الفاعل مرفوع *)
Definition is_valid_faail (n : NounPhrase) : Prop :=
  noun_case n = Nominative.

(* التحقق من أن المفعول به منصوب *)
Definition is_valid_mafoul_bih (n : NounPhrase) : Prop :=
  noun_case n = Accusative.

(* ============================================================ *)
(* الجزء الخامس: نظريات صحة الجملة الاسمية                      *)
(* Part 5: Nominal Sentence Validity Theorems                    *)
(* ============================================================ *)

(* نظرية: الجملة الاسمية صحيحة إذا كان المبتدأ والخبر مرفوعين *)
Definition valid_nominal_sentence (s : NominalSentence) : Prop :=
  is_valid_mubtada (mubtada s) /\ is_valid_khabar (khabar s).

(* إثبات نظرية الجملة الاسمية *)
Theorem nominal_sentence_theorem :
  forall (m k : NounPhrase),
    noun_case m = Nominative ->
    noun_case k = Nominative ->
    valid_nominal_sentence (mkNominal m k).
Proof.
  intros m k Hm Hk.
  unfold valid_nominal_sentence.
  unfold is_valid_mubtada, is_valid_khabar.
  simpl.
  split; assumption.
Qed.

(* ============================================================ *)
(* الجزء السادس: نظريات صحة الجملة الفعلية                      *)
(* Part 6: Verbal Sentence Validity Theorems                     *)
(* ============================================================ *)

(* نظرية: الجملة الفعلية صحيحة إذا كان الفاعل مرفوعاً *)
Definition valid_verbal_sentence (s : VerbalSentence) : Prop :=
  is_valid_faail (faail s).

(* إثبات نظرية الجملة الفعلية *)
Theorem verbal_sentence_theorem :
  forall (v : VerbPhrase) (f : NounPhrase),
    noun_case f = Nominative ->
    valid_verbal_sentence (mkVerbal v f).
Proof.
  intros v f Hf.
  unfold valid_verbal_sentence.
  unfold is_valid_faail.
  simpl.
  assumption.
Qed.

(* ============================================================ *)
(* الجزء السابع: نظريات صحة الجملة الفعلية المتعدية             *)
(* Part 7: Transitive Sentence Validity Theorems                 *)
(* ============================================================ *)

(* نظرية: الجملة الفعلية المتعدية صحيحة إذا كان الفاعل مرفوعاً والمفعول به منصوباً *)
Definition valid_transitive_sentence (s : TransitiveSentence) : Prop :=
  is_valid_faail (t_faail s) /\ is_valid_mafoul_bih (mafoul_bih s).

(* إثبات نظرية الجملة الفعلية المتعدية *)
Theorem transitive_sentence_theorem :
  forall (v : VerbPhrase) (f m : NounPhrase),
    noun_case f = Nominative ->
    noun_case m = Accusative ->
    valid_transitive_sentence (mkTransitive v f m).
Proof.
  intros v f m Hf Hm.
  unfold valid_transitive_sentence.
  unfold is_valid_faail, is_valid_mafoul_bih.
  simpl.
  split; assumption.
Qed.

(* ============================================================ *)
(* الجزء الثامن: أمثلة تطبيقية                                  *)
(* Part 8: Practical Examples                                    *)
(* ============================================================ *)

(* مثال: "الكتابُ جديدٌ" - The book is new *)
Example kitab_jadid :
  let mubtada := mkNoun "كتاب" Nominative Masculine Singular true in
  let khabar := mkNoun "جديد" Nominative Masculine Singular false in
  valid_nominal_sentence (mkNominal mubtada khabar).
Proof.
  unfold valid_nominal_sentence.
  unfold is_valid_mubtada, is_valid_khabar.
  simpl.
  split; reflexivity.
Qed.

(* مثال: "جاء الطالبُ" - The student came *)
Example jaa_altaalib :
  let verb := mkVerb "جاء" Past Masculine Singular in
  let faail := mkNoun "طالب" Nominative Masculine Singular true in
  valid_verbal_sentence (mkVerbal verb faail).
Proof.
  unfold valid_verbal_sentence.
  unfold is_valid_faail.
  simpl.
  reflexivity.
Qed.

(* مثال: "قرأ الطالبُ الكتابَ" - The student read the book *)
Example qara_altaalib_alkitab :
  let verb := mkVerb "قرأ" Past Masculine Singular in
  let faail := mkNoun "طالب" Nominative Masculine Singular true in
  let mafoul := mkNoun "كتاب" Accusative Masculine Singular true in
  valid_transitive_sentence (mkTransitive verb faail mafoul).
Proof.
  unfold valid_transitive_sentence.
  unfold is_valid_faail, is_valid_mafoul_bih.
  simpl.
  split; reflexivity.
Qed.

(* ============================================================ *)
(* نهاية الملف - End of File                                    *)
(* ============================================================ *)
