module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0208
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0209
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVCrdE

open TVCrdAlg TVCrdLoc TVCrdGerm

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {r : ℕ}

theorem memW {f : (Fin r → ℂ) → X} (h : f ∈ WSm r X) :
    ContDiffOn ℝ ∞ f (OmX r) ∧ ∀ x, x ∉ OmX r → f x = 0 := h

def opE (l : Fin r) (i : Fin 6) : Module.End ℂ (WSm r X) where
  toFun f := ⟨opL l i f, preserved_operators_holds r X l i f f.2⟩
  map_add' f g := Subtype.ext (linear_operators_holds r X l i f g 1 f.2 g.2).1
  map_smul' a f := Subtype.ext (linear_operators_holds r X l i f f a f.2 f.2).2

theorem opL_three (l : Fin r) : opL (E := X) l 3 = pbOp l := rfl
theorem opL_four (l : Fin r) : opL (E := X) l 4 = cbOp l := rfl
theorem opL_five (l : Fin r) : opL (E := X) l 5 = cbiOp l := rfl

def mulE (a : (Fin r → ℂ) → ℂ) (ha : ContDiffOn ℝ ∞ a (OmX r)) : Module.End ℂ (WSm r X) where
  toFun f := ⟨fun x => a x • (f : (Fin r → ℂ) → X) x,
    ⟨ha.smul (memW f.2).1, fun x hx => by simp [(memW f.2).2 x hx]⟩⟩
  map_add' f g := Subtype.ext (funext fun x => by simp [smul_add])
  map_smul' s f := Subtype.ext (funext fun x => by simp [smul_comm (a x) s])

theorem comm_of_mul (A B : Module.End ℂ (WSm r X)) (a b : (Fin r → ℂ) → ℂ)
    (hA : ∀ (f : WSm r X) x, (A f : (Fin r → ℂ) → X) x = a x • (f : (Fin r → ℂ) → X) x)
    (hB : ∀ (f : WSm r X) x, (B f : (Fin r → ℂ) → X) x = b x • (f : (Fin r → ℂ) → X) x) : Commute A B := by
  refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
  show (A (B f) : (Fin r → ℂ) → X) x = (B (A f) : (Fin r → ℂ) → X) x
  rw [hA, hB, hB, hA, smul_smul, smul_smul, mul_comm]

def PN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 3 else 0
def CbN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 4 else 0
def CbiN (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (i : ℕ) : Module.End ℂ (WSm r X) :=
  if h : i < r then opE ⟨i, h⟩ 5 else 0

theorem PN_coe (i : ℕ) (f : WSm r X) : ((PN r X i f : WSm r X) : (Fin r → ℂ) → X) = pbN r i f := by
  unfold PN pbN; split_ifs <;> rfl
theorem CbN_coe (i : ℕ) (f : WSm r X) : ((CbN r X i f : WSm r X) : (Fin r → ℂ) → X) = cbN r i f := by
  unfold CbN cbN; split_ifs <;> rfl
theorem CbiN_coe (i : ℕ) (f : WSm r X) : ((CbiN r X i f : WSm r X) : (Fin r → ℂ) → X) = cbiN r i f := by
  unfold CbiN cbiN; split_ifs <;> rfl

theorem CbN_mul (i : ℕ) (f : WSm r X) (x : Fin r → ℂ) :
    (CbN r X i f : (Fin r → ℂ) → X) x = (if h : i < r then star (x ⟨i, h⟩) else 0) • (f : (Fin r → ℂ) → X) x := by
  unfold CbN
  split_ifs
  · rfl
  · simp
theorem CbiN_mul (i : ℕ) (f : WSm r X) (x : Fin r → ℂ) :
    (CbiN r X i f : (Fin r → ℂ) → X) x =
      (if h : i < r then (star (x ⟨i, h⟩))⁻¹ else 0) • (f : (Fin r → ℂ) → X) x := by
  unfold CbiN
  split_ifs
  · rfl
  · simp

theorem comm_PN_CbN {i j : ℕ} (h : i ≠ j) : Commute (PN r X i) (CbN r X j) := by
  unfold PN CbN
  split_ifs with h1 h2
  · refine LinearMap.ext fun f => Subtype.ext ?_
    exact commuting_functional_holds r X ⟨i, h1⟩ ⟨j, h2⟩ 3 4 f f.2 (Or.inl fun e => h (congrArg Fin.val e))
  all_goals simp
theorem comm_PN_CbiN {i j : ℕ} (h : i ≠ j) : Commute (PN r X i) (CbiN r X j) := by
  unfold PN CbiN
  split_ifs with h1 h2
  · refine LinearMap.ext fun f => Subtype.ext ?_
    exact commuting_functional_holds r X ⟨i, h1⟩ ⟨j, h2⟩ 3 5 f f.2 (Or.inl fun e => h (congrArg Fin.val e))
  all_goals simp

theorem comm_CbN_CbN (i j : ℕ) : Commute (CbN r X i) (CbN r X j) := comm_of_mul _ _ _ _ (CbN_mul i) (CbN_mul j)
theorem comm_CbN_CbiN (i j : ℕ) : Commute (CbN r X i) (CbiN r X j) := comm_of_mul _ _ _ _ (CbN_mul i) (CbiN_mul j)
theorem comm_CbiN_CbiN (i j : ℕ) : Commute (CbiN r X i) (CbiN r X j) :=
  comm_of_mul _ _ _ _ (CbiN_mul i) (CbiN_mul j)

def Gop (k r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] : Module.End ℂ (WSm r X) :=
  mulE (gaugeF k r) gaugeF_smooth

theorem comm_G_CbN (k i : ℕ) : Commute (Gop k r X) (CbN r X i) :=
  comm_of_mul _ _ (gaugeF k r) _ (fun _ _ => rfl) (CbN_mul i)
theorem comm_G_CbiN (k i : ℕ) : Commute (Gop k r X) (CbiN r X i) :=
  comm_of_mul _ _ (gaugeF k r) _ (fun _ _ => rfl) (CbiN_mul i)

def sG (k r : ℕ) (i : Fin r) : ℂ := ((Mdim k r i - 1 : ℕ) : ℂ) / 2

theorem P_G (k : ℕ) (i : Fin r) : opE i 3 * Gop k r X = Gop k r X * opE i 3 + sG k r i • Gop k r X := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  show pbOp i (fun x => gaugeF k r x • (f : (Fin r → ℂ) → X) x) = _
  rw [pbOp_gauge i _ f.2]
  funext x
  simp [Gop, mulE, opE, opL_three, sG]

theorem G_PN (k : ℕ) {i : ℕ} (hi : i < r) :
    Gop k r X * PN r X i = (PN r X i - sG k r ⟨i, hi⟩ • 1) * Gop k r X := by
  have h := P_G (X := X) k ⟨i, hi⟩
  have hP : PN r X i = opE ⟨i, hi⟩ 3 := dite_eq_left hi
  rw [hP, sub_mul, smul_mul_assoc, one_mul, h]
  abel

def Dd (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (y : ℂ) (j : ℕ) : Module.End ℂ (WSm r X) :=
  y • 1 - PN r X j
def Ee (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (j : ℕ) : Module.End ℂ (WSm r X) :=
  CbN r X j * CbiN r X (j - 1)
def Dw (r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (w : ℂ) (m : ℕ) : Module.End ℂ (WSm r X) :=
  (w - (m : ℂ)) • 1 - PN r X (r - m - 1)

theorem hDe (y : ℂ) : ∀ i j, i + 1 ≤ j → Dd r X y j * Ee r X i = Ee r X i * Dd r X y j := by
  intro i j hij
  have : Commute (Dd r X y j) (Ee r X i) := by
    unfold Dd Ee
    refine Commute.sub_left ((Commute.one_left _).smul_left y) ?_
    exact (comm_PN_CbN (by omega)).mul_right (comm_PN_CbiN (by omega))
  exact this.eq

theorem hee : ∀ i j, Ee r X i * Ee r X j = Ee r X j * Ee r X i := by
  intro i j
  have : Commute (Ee r X i) (Ee r X j) := by
    unfold Ee
    refine Commute.mul_left ?_ ?_
    · exact (comm_CbN_CbN i j).mul_right (comm_CbN_CbiN i (j - 1))
    · exact ((comm_CbN_CbiN j (i - 1)).symm).mul_right (comm_CbiN_CbiN (i - 1) (j - 1))
  exact this.eq

theorem hGe (k : ℕ) : ∀ j, Gop k r X * Ee r X j = Ee r X j * Gop k r X := by
  intro j
  exact ((comm_G_CbN k j).mul_right (comm_G_CbiN k (j - 1))).eq

theorem shift_eq (k : ℕ) (y : ℂ) {m : ℕ} (hm : m < r) :
    kvTop k r y - (m : ℂ) + sG k r ⟨r - m - 1, by omega⟩ = y := by
  have h : Mdim k r ⟨r - m - 1, by omega⟩ - 1 = 2 * m + k + 2 := by
    simp only [Mdim]; omega
  simp only [sG, kvTop, h]
  push_cast
  ring

theorem hG (k : ℕ) (y : ℂ) : ∀ m < r,
    Gop k r X * Dw r X (kvTop k r y) m = Dd r X y (r - m - 1) * Gop k r X := by
  intro m hm
  unfold Dw Dd
  rw [mul_sub, mul_smul_comm, mul_one, G_PN k (show r - m - 1 < r by omega), sub_mul, sub_mul, smul_mul_assoc,
    smul_mul_assoc, one_mul]
  have hy := shift_eq (r := r) k y hm
  conv_rhs => rw [← hy]
  rw [add_smul]
  abel

theorem iteratedOperator_coe (w : ℂ) : ∀ (m : ℕ) (f : WSm r X),
    (kvP r w m).1 (f : (Fin r → ℂ) → X) = ((topK (Dw r X w) (Ee r X) r m).1 f : WSm r X) ∧
      (kvP r w m).2 (f : (Fin r → ℂ) → X) = ((topK (Dw r X w) (Ee r X) r m).2 f : WSm r X) := by
  intro m
  induction m with
  | zero =>
    intro f
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    intro f
    have hD : (fun c => (w - (m : ℂ)) • (f : (Fin r → ℂ) → X) c - pbN r (r - m - 1) (f : (Fin r → ℂ) → X) c) =
        ((Dw r X w m f : WSm r X) : (Fin r → ℂ) → X) := by
      funext c
      simp [Dw, PN_coe]
    simp only [kvP, topK, Ee, LinearMap.sub_apply, mul_apply_eq_comp, Submodule.coe_sub]
    refine ⟨?_, (ih f).1⟩
    rw [hD, (ih (Dw r X w m f)).1, (ih f).2, ← CbiN_coe, ← CbN_coe]

theorem vABm_coe (y : ℂ) : ∀ (i : ℕ) (f : WSm r X),
    (vABm r y i).1 (f : (Fin r → ℂ) → X) = ((botA (Dd r X y) (CbN r X) (CbiN r X) r i).1 f : WSm r X) ∧
      (vABm r y i).2 (f : (Fin r → ℂ) → X) = ((botA (Dd r X y) (CbN r X) (CbiN r X) r i).2 f : WSm r X) := by
  intro i
  induction i with
  | zero =>
    intro f
    exact ⟨rfl, rfl⟩
  | succ i ih =>
    intro f
    by_cases h : i < r
    · obtain ⟨h1, h2⟩ := ih f
      have hP : PN r X i = opE ⟨i, h⟩ 3 := dite_eq_left h
      have hC : CbN r X i = opE ⟨i, h⟩ 4 := dite_eq_left h
      have hCi : CbiN r X i = opE ⟨i, h⟩ 5 := dite_eq_left h
      simp only [vABm, dite_eq_left h, botA, ite_eq_left h]
      rw [h1, h2]
      refine ⟨?_, ?_⟩
      · simp [Dd, hP, hC, opE, opL_three, opL_four]
      · simp [hCi, opE, opL_five]
    · simpa only [vABm, dite_eq_right h, botA, ite_eq_right h] using ih f

end Formalism.FourierDecayAlt.P.CutMP.TVCrdE

namespace Formalism.FourierDecayAlt.P.CutMP

open TVCrdAlg TVCrdLoc TVCrdGerm TVCrdE

theorem toda_coordinate_holds : TVCrd := by
  intro k r X _ _ y Φ U c hU hUO hc hΨ
  obtain ⟨φ, hφ, hΦ, hΨφ⟩ := TVCrdLoc.loc (k := k) Φ U c hU hUO hc hΨ
  have hKvGerm : ∀ (m : ℕ) (u v : (Fin r → ℂ) → X), u =ᶠ[𝓝 c] v →
      (kvP r (kvTop k r y) m).1 u =ᶠ[𝓝 c] (kvP r (kvTop k r y) m).1 v ∧
      (kvP r (kvTop k r y) m).2 u =ᶠ[𝓝 c] (kvP r (kvTop k r y) m).2 v := by
    intro m
    induction m with
    | zero =>
      intro u v huv
      exact ⟨huv, EventuallyEq.rfl⟩
    | succ m ih =>
      intro u v huv
      have hIn : (fun x => (kvTop k r y - (m : ℂ)) • u x - pbN r (r - m - 1) u x) =ᶠ[𝓝 c]
          (fun x => (kvTop k r y - (m : ℂ)) • v x - pbN r (r - m - 1) v x) := by
        filter_upwards [huv, pbN_germ (r - m - 1) huv] with x h1 h2
        rw [h1, h2]
      obtain ⟨h1, h2⟩ := ih u v huv
      have hCb := cbN_germ (r - m) (cbiN_germ (r - m - 1) h2)
      simp only [kvP]
      refine ⟨?_, h1⟩
      filter_upwards [(ih _ _ hIn).1, hCb] with x h3 h4
      simp only [Pi.sub_apply]
      rw [h3, h4]
  have hABGerm : ∀ (i : ℕ) (u v : (Fin r → ℂ) → X), u =ᶠ[𝓝 c] v →
      (vABm r y i).1 u =ᶠ[𝓝 c] (vABm r y i).1 v ∧ (vABm r y i).2 u =ᶠ[𝓝 c] (vABm r y i).2 v := by
    intro i
    induction i with
    | zero =>
      intro u v huv
      exact ⟨huv, EventuallyEq.rfl⟩
    | succ i ih =>
      intro u v huv
      obtain ⟨h1, h2⟩ := ih u v huv
      by_cases hi : i < r
      · simp only [vABm, dite_eq_left hi]
        refine ⟨?_, cbiOp_germ ⟨i, hi⟩ h1⟩
        filter_upwards [h1, pbOp_germ ⟨i, hi⟩ h1, cbOp_germ ⟨i, hi⟩ h2] with x h3 h4 h5
        simp only [Pi.sub_apply, Pi.smul_apply]
        rw [h3, h4, h5]
      · simpa only [vABm, dite_eq_right hi] using And.intro h1 h2
  have eL : kvC r (kvTop k r y) r Φ c = kvC r (kvTop k r y) r φ c :=
    (hKvGerm r Φ φ hΦ).1.eq_of_nhds
  have eR : (vABm r y r).1 (fun c' => gaugeF k r c' • Φ c') c =
      (vABm r y r).1 (fun c' => gaugeF k r c' • φ c') c :=
    (hABGerm r _ _ hΨφ).1.eq_of_nhds
  rw [eL, eR]
  let f : WSm r X := ⟨φ, hφ⟩
  have hK : kvC r (kvTop k r y) r φ = ((topK (Dw r X (kvTop k r y)) (Ee r X) r r).1 f : WSm r X) :=
    (iteratedOperator_coe (kvTop k r y) r f).1
  have hA : (vABm r y r).1 (fun c' => gaugeF k r c' • φ c') =
      ((botA (Dd r X y) (CbN r X) (CbiN r X) r r).1 (Gop k r X f) : WSm r X) :=
    (vABm_coe y r (Gop k r X f)).1
  let D := Dd r X y
  let e := Ee r X
  let Dt := fun m => D (r - m - 1)
  let B := botA D (CbN r X) (CbiN r X) r
  have hBot : ∀ i, i ≤ r → (B i).1 = cont D e 0 i ∧
      (B i).2 = if i = 0 then 0 else CbiN r X (i - 1) * cont D e 0 (i - 1) := by
    intro i
    induction i with
    | zero => simp [B, botA, cont_zero]
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      simp only [B, botA, ite_eq_left (show i < r by omega)] at *
      refine ⟨?_, ?_⟩
      · rw [h1, h2]
        cases i with
        | zero => simp [cont_zero, cont_one]
        | succ i => simp [cont_two, e, Ee, mul_assoc]
      · simp [h1]
  have hCont : ∀ n a, cont D e a (n + 2) = cont D e (a + 1) (n + 1) * D a -
      e (a + 1) * cont D e (a + 2) n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      intro a
      rw [cont_two, cont_one, cont_one, cont_zero, cont_zero, add_zero]
    | one =>
      intro a
      change cont D e a 3 = cont D e (a + 1) 2 * D a - e (a + 1) * cont D e (a + 2) 1
      have h1 : cont D e a 3 = D (a + 2) * (D (a + 1) * D a - e (a + 1) * 1) - e (a + 2) * D a := rfl
      have h2 : cont D e (a + 1) 2 = D (a + 2) * D (a + 1) - e (a + 2) * 1 := rfl
      have hComm : D (a + 2) * e (a + 1) = e (a + 1) * D (a + 2) := hDe y _ _ (by omega)
      rw [h1, h2, cont_one]
      simp only [mul_one, mul_sub, sub_mul, ← mul_assoc, hComm]
      abel
    | more n ih0 ih1 =>
      intro a
      have h1 : cont D e a (n + 2 + 2) =
          D (a + n + 3) * cont D e a (n + 1 + 2) - e (a + n + 3) * cont D e a (n + 2) := rfl
      have h2 : cont D e (a + 1) (n + 2 + 1) =
          D (a + n + 3) * cont D e (a + 1) (n + 2) - e (a + n + 3) * cont D e (a + 1) (n + 1) := by
        rw [show n + 2 + 1 = (n + 1) + 2 by omega, cont_two, show a + 1 + (n + 1) + 1 = a + n + 3 by omega]
      have h3 : cont D e (a + 2) (n + 2) =
          D (a + n + 3) * cont D e (a + 2) (n + 1) - e (a + n + 3) * cont D e (a + 2) n := by
        rw [cont_two, show a + 2 + n + 1 = a + n + 3 by omega]
      have hCommD : D (a + n + 3) * e (a + 1) = e (a + 1) * D (a + n + 3) := hDe y _ _ (by omega)
      have hCommE : e (a + n + 3) * e (a + 1) = e (a + 1) * e (a + n + 3) := hee _ _
      rw [h1, h2, h3, ih1 a, ih0 a]
      simp only [mul_sub, sub_mul, ← mul_assoc, hCommD, hCommE]
      abel
  have hTop : ∀ m, m ≤ r → (topK Dt e r m).1 = cont D e (r - m) m ∧
      (topK Dt e r m).2 = if m = 0 then 0 else cont D e (r - m + 1) (m - 1) := by
    intro m
    induction m with
    | zero => simp [topK, cont_zero]
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      simp only [topK]
      refine ⟨?_, ?_⟩
      · rw [h1, h2]
        cases m with
        | zero => simp [Dt, cont_zero, cont_one]
        | succ m =>
          have ha : r - (m + 1 + 1) + 1 = r - (m + 1) := by omega
          have hb : r - (m + 1 + 1) + 2 = r - (m + 1) + 1 := by omega
          simp only [Dt, Nat.succ_ne_zero, Nat.add_sub_cancel]
          rw [hCont m (r - (m + 1 + 1)), ha, hb]
          rfl
      · simpa only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
          show r - (m + 1) + 1 = r - m by omega] using h1
  let G := Gop k r X
  let T := topK (Dw r X (kvTop k r y)) e r
  have hConj : ∀ m, m ≤ r → G * (T m).1 = (topK Dt e r m).1 * G ∧
      G * (T m).2 = (topK Dt e r m).2 * G := by
    intro m
    induction m with
    | zero => simp [T, topK]
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      simp only [T, topK] at *
      refine ⟨?_, h1⟩
      have hGD : G * Dw r X (kvTop k r y) m = Dt m * G := hG k y m (by omega)
      have hGE : G * e (r - m) = e (r - m) * G := hGe k _
      rw [mul_sub, ← mul_assoc, h1, mul_assoc, hGD, ← mul_assoc G (e (r - m)), hGE,
        mul_assoc (e (r - m)) G, h2, sub_mul, mul_assoc, mul_assoc]
  have hC := (hConj r le_rfl).1
  have hAT : (botA (Dd r X y) (CbN r X) (CbiN r X) r r).1 =
      (topK (fun m => Dd r X y (r - m - 1)) (Ee r X) r r).1 := by
    change (B r).1 = (topK Dt e r r).1
    rw [(hBot r le_rfl).1, (hTop r le_rfl).1, Nat.sub_self]
  rw [hK, hA, hAT]
  have h2 : (topK (fun m => Dd r X y (r - m - 1)) (Ee r X) r r).1 (Gop k r X f) =
      Gop k r X ((topK (Dw r X (kvTop k r y)) (Ee r X) r r).1 f) := by
    change (topK Dt e r r).1 (G f) = G ((T r).1 f)
    rw [← mul_apply_eq_comp, ← hC, mul_apply_eq_comp]
  rw [h2]
  rfl

end Formalism.FourierDecayAlt.P.CutMP
