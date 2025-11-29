(* ============================================================ *)
(* MorphologyRules.v - قواعد الصرف                              *)
(* Morphological Rules (Dual, Plurals, etc.)                    *)
(* ============================================================ *)

Require Import Coq.Strings.String.
Require Import ArabicGrammar.ArabicGrammar.

(* ============================================================ *)
(* الجزء الأول: علامات الإعراب الفرعية                          *)
(* Part 1: Secondary Case Markers                                *)
(* ============================================================ *)

(* علامات الإعراب - Case Markers *)
Inductive CaseMarker : Type :=
  | Damma      (* ضمة - للرفع في المفرد *)
  | Fatha      (* فتحة - للنصب في المفرد *)
  | Kasra      (* كسرة - للجر في المفرد *)
  | Alif       (* ألف - للرفع في المثنى *)
  | Ya_dual    (* ياء - للنصب والجر في المثنى *)
  | Waw        (* واو - للرفع في جمع المذكر السالم *)
  | Ya_plural  (* ياء - للنصب والجر في جمع المذكر السالم *)
  | Sukun.     (* سكون - للجزم *)

(* ============================================================ *)
(* الجزء الثاني: قواعد المثنى                                   *)
(* Part 2: Dual Form Rules                                       *)
(* ============================================================ *)

(* المثنى يرفع بالألف وينصب ويجر بالياء *)
Definition dual_nominative_marker : CaseMarker := Alif.
Definition dual_accusative_marker : CaseMarker := Ya_dual.
Definition dual_genitive_marker : CaseMarker := Ya_dual.

(* التحقق من صحة إعراب المثنى *)
Definition is_valid_dual_case (c : Case) (m : CaseMarker) : Prop :=
  match c with
  | Nominative => m = Alif
  | Accusative => m = Ya_dual
  | Genitive => m = Ya_dual
  end.

(* نظرية المثنى *)
Theorem dual_case_theorem :
  forall (n : NounPhrase),
    noun_number n = Dual ->
    (noun_case n = Nominative -> is_valid_dual_case Nominative Alif) /\
    (noun_case n = Accusative -> is_valid_dual_case Accusative Ya_dual) /\
    (noun_case n = Genitive -> is_valid_dual_case Genitive Ya_dual).
Proof.
  intros n Hdual.
  split.
  - intros _. unfold is_valid_dual_case. reflexivity.
  - split.
    + intros _. unfold is_valid_dual_case. reflexivity.
    + intros _. unfold is_valid_dual_case. reflexivity.
Qed.

(* مثال: "جاء الطالبان" - The two students came *)
Example dual_nominative_example :
  is_valid_dual_case Nominative Alif.
Proof.
  unfold is_valid_dual_case.
  reflexivity.
Qed.

(* ============================================================ *)
(* الجزء الثالث: قواعد جمع المذكر السالم                        *)
(* Part 3: Sound Masculine Plural Rules                          *)
(* ============================================================ *)

(* جمع المذكر السالم يرفع بالواو وينصب ويجر بالياء *)
Definition masc_plural_nominative_marker : CaseMarker := Waw.
Definition masc_plural_accusative_marker : CaseMarker := Ya_plural.
Definition masc_plural_genitive_marker : CaseMarker := Ya_plural.

(* التحقق من صحة إعراب جمع المذكر السالم *)
Definition is_valid_masc_plural_case (c : Case) (m : CaseMarker) : Prop :=
  match c with
  | Nominative => m = Waw
  | Accusative => m = Ya_plural
  | Genitive => m = Ya_plural
  end.

(* نظرية جمع المذكر السالم *)
Theorem masc_plural_case_theorem :
  (is_valid_masc_plural_case Nominative Waw) /\
  (is_valid_masc_plural_case Accusative Ya_plural) /\
  (is_valid_masc_plural_case Genitive Ya_plural).
Proof.
  split.
  - unfold is_valid_masc_plural_case. reflexivity.
  - split.
    + unfold is_valid_masc_plural_case. reflexivity.
    + unfold is_valid_masc_plural_case. reflexivity.
Qed.

(* مثال: "جاء المعلمون" - The teachers came *)
Example masc_plural_nominative_example :
  is_valid_masc_plural_case Nominative Waw.
Proof.
  unfold is_valid_masc_plural_case.
  reflexivity.
Qed.

(* ============================================================ *)
(* الجزء الرابع: قواعد جمع المؤنث السالم                        *)
(* Part 4: Sound Feminine Plural Rules                           *)
(* ============================================================ *)

(* جمع المؤنث السالم يرفع بالضمة وينصب ويجر بالكسرة *)
Definition fem_plural_nominative_marker : CaseMarker := Damma.
Definition fem_plural_accusative_marker : CaseMarker := Kasra.  (* خاص بجمع المؤنث *)
Definition fem_plural_genitive_marker : CaseMarker := Kasra.

(* التحقق من صحة إعراب جمع المؤنث السالم *)
Definition is_valid_fem_plural_case (c : Case) (m : CaseMarker) : Prop :=
  match c with
  | Nominative => m = Damma
  | Accusative => m = Kasra  (* ينصب بالكسرة نيابة عن الفتحة *)
  | Genitive => m = Kasra
  end.

(* نظرية جمع المؤنث السالم *)
Theorem fem_plural_case_theorem :
  (is_valid_fem_plural_case Nominative Damma) /\
  (is_valid_fem_plural_case Accusative Kasra) /\
  (is_valid_fem_plural_case Genitive Kasra).
Proof.
  split.
  - unfold is_valid_fem_plural_case. reflexivity.
  - split.
    + unfold is_valid_fem_plural_case. reflexivity.
    + unfold is_valid_fem_plural_case. reflexivity.
Qed.

(* مثال: "جاءت المعلماتُ" - The female teachers came *)
Example fem_plural_nominative_example :
  is_valid_fem_plural_case Nominative Damma.
Proof.
  unfold is_valid_fem_plural_case.
  reflexivity.
Qed.

(* مثال: "رأيتُ المعلماتِ" - I saw the female teachers *)
(* جمع المؤنث السالم ينصب بالكسرة *)
Example fem_plural_accusative_example :
  is_valid_fem_plural_case Accusative Kasra.
Proof.
  unfold is_valid_fem_plural_case.
  reflexivity.
Qed.

(* ============================================================ *)
(* نهاية الملف - End of File                                    *)
(* ============================================================ *)
