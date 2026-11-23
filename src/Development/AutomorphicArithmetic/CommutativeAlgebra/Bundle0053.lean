module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0073
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CongruenceCRTOfLatticeGen
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

namespace UpperTheory.Gal.Int.Geo.CRT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private theorem isInt_one' : IsIntAf (1 : AfP p) := fun v => by
  rw [map_one]; exact one_mem _

private theorem inAf_mem' (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isInt_one', rfl⟩

private theorem mulF_tmul (c : 𝓞 D.F) (a : AfP p) (t : ℚ) (x : D.La) :
    mulF D c (a ⊗ₜ (t ⊗ₜ x)) = a ⊗ₜ (t ⊗ₜ (algebraMap (𝓞 D.F) D.O c • x)) := by
  simp [mulF, actQ]

private theorem mulF_inAf (c : 𝓞 D.F) (x : D.La) :
    mulF D c (inAf D x) = inAf D (algebraMap (𝓞 D.F) D.O c • x) := mulF_tmul c 1 1 x

private theorem vq_induction {P : AfP p ⊗[ℚ] VQ D → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (ht : ∀ (a : AfP p) (t : ℚ) (x : D.La), P (a ⊗ₜ (t ⊗ₜ x))) (v : AfP p ⊗[ℚ] VQ D) : P v :=
  _root_.UpperTheory.Reformulated.B.Qk61.vq_induction h0 hadd ht v

private theorem mulF_mul (c d : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) : mulF D (c * d) v = mulF D c (mulF D d v) := by
  refine vq_induction (P := fun v => mulF D (c * d) v = mulF D c (mulF D d v)) (by simp) ?_ ?_ v
  · intro x y hx hy; simp only [map_add (f := _), hx, hy]
  · intro a t x; simp only [mulF_tmul, map_mul, mul_smul]

private theorem mulF_add (c d : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) : mulF D (c + d) v = mulF D c v + mulF D d v := by
  refine vq_induction (P := fun v => mulF D (c + d) v = mulF D c v + mulF D d v) (by simp) ?_ ?_ v
  · intro x y hx hy; simp only [map_add (f := _), hx, hy]; abel
  · intro a t x; simp only [mulF_tmul, map_add (f := _), add_smul, TensorProduct.tmul_add]

private theorem mulF_one (v : AfP p ⊗[ℚ] VQ D) : mulF D 1 v = v := by
  refine vq_induction (P := fun v => mulF D 1 v = v) (by simp) ?_ ?_ v
  · intro x y hx hy; simp only [map_add (f := _), hx, hy]
  · intro a t x; simp only [mulF_tmul, map_one, one_smul]

private theorem mulF_nat (n : ℕ) (v : AfP p ⊗[ℚ] VQ D) : mulF D (n : 𝓞 D.F) v = n • v := by
  induction n with
  | zero =>
    refine vq_induction (P := fun v => mulF D ((0 : ℕ) : 𝓞 D.F) v = (0 : ℕ) • v) (by simp) ?_ ?_ v
    · intro x y hx hy; simp only [map_add (f := _), hx, hy]; simp
    · intro a t x; simp [mulF_tmul]
  | succ n ih => rw [Nat.cast_succ, mulF_add, mulF_one, ih, succ_nsmul]

private theorem mulF_mem (c : 𝓞 D.F) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) : mulF D c v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [mulF_tmul]
    exact AddSubgroup.subset_closure ⟨a, _, ha, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

private theorem mem_idHat {𝔟 : Ideal (𝓞 D.F)} {x : 𝓞 D.F} (hx : x ∈ 𝔟) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    mulF D x v ∈ idHat D 𝔟 := AddSubgroup.subset_closure ⟨x, hx, v, hv, rfl⟩

private theorem idHat_ind {𝔟 : Ideal (𝓞 D.F)} {S : AddSubgroup (AfP p ⊗[ℚ] VQ D)}
    (h : ∀ x ∈ 𝔟, ∀ v ∈ LaHat D, mulF D x v ∈ S) : idHat D 𝔟 ≤ S :=
  (AddSubgroup.closure_le _).2 (by rintro _ ⟨x, hx, v, hv, rfl⟩; exact h x hx v hv)

private theorem idHat_mono {𝔟 𝔠 : Ideal (𝓞 D.F)} (h : 𝔟 ≤ 𝔠) : idHat D 𝔟 ≤ idHat D 𝔠 :=
  idHat_ind fun _ hx _ hv => mem_idHat (h hx) hv

private theorem mulF_mem_idHat_mul {𝔟 𝔠 : Ideal (𝓞 D.F)} {c : 𝓞 D.F} (hc : c ∈ 𝔠) {v : AfP p ⊗[ℚ] VQ D}
    (hv : v ∈ idHat D 𝔟) : mulF D c v ∈ idHat D (𝔠 * 𝔟) := by
  have : idHat D 𝔟 ≤ (idHat D (𝔠 * 𝔟)).comap (mulF D c).toAddMonoidHom := idHat_ind fun x hx w hw => by
    change mulF D c (mulF D x w) ∈ idHat D (𝔠 * 𝔟)
    rw [← mulF_mul]
    exact mem_idHat (Ideal.mul_mem_mul hc hx) hw
  exact this hv

private theorem actOn_comm (L : Link D G) (y : AfP p ⊗[ℚ] G.C) (b : D.O) :
    actOn L.rep (AfP p) y * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * actOn L.rep (AfP p) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), add_mul, mul_add, hx, hy]
  | tmul r c =>
    have e : actOn L.rep (AfP p) (r ⊗ₜ c) = r • (L.rep c).baseChange (AfP p) := by
      have e0 : actOn L.rep (AfP p) (r ⊗ₜ c) =
          (Algebra.ofId (AfP p) (Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) r) * (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) (L.rep c) :=
        Algebra.TensorProduct.lift_tmul _ _ _ _ _
      rw [e0, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, _root_.one_mul]
      rfl
    have h := (L.rep_range (L.rep c)).1 ⟨c, rfl⟩ b
    have h2 : (L.rep c).baseChange (AfP p) * (actQ D b).baseChange (AfP p) =
        (actQ D b).baseChange (AfP p) * (L.rep c).baseChange (AfP p) := by
      have := congrArg (Module.End.baseChangeHom ℚ (AfP p) (VQ D)) h
      rw [map_mul, map_mul] at this
      exact this
    rw [e, smul_mul_assoc, mul_smul_comm, h2]

private theorem actG_mulF (L : Link D G) (g : G.GAf) (c : 𝓞 D.F) (v : AfP p ⊗[ℚ] VQ D) :
    L.actG g (mulF D c v) = mulF D c (L.actG g v) :=
  LinearMap.congr_fun (actOn_comm L _ (algebraMap (𝓞 D.F) D.O c)) v

private theorem wSub_inAf {𝔞 : Ideal (𝓞 D.F)} {y : D.La} (hy : y ∈ wSub D 𝔞 1) : inAf D y ∈ idHat D 𝔞 := by
  have key : ∀ b : D.O, inAf D (b • y) ∈ idHat D 𝔞 := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, z', rfl⟩ := hz
      intro b
      rw [pow_one] at hc
      have e : b • algebraMap (𝓞 D.F) D.O c • z' = algebraMap (𝓞 D.F) D.O c • b • z' := by
        rw [smul_smul, smul_smul, Algebra.commutes]
      rw [e, ← mulF_inAf]
      exact mem_idHat hc (inAf_mem' _)
    | zero =>
      intro b
      rw [smul_zero]
      have : inAf D (0 : D.La) = 0 := by simp [inAf]
      rw [this]; exact zero_mem _
    | add x z _ _ hx hz =>
      intro b
      have : inAf D (b • (x + z)) = inAf D (b • x) + inAf D (b • z) := by
        simp [inAf, smul_add, TensorProduct.tmul_add]
      rw [this]; exact add_mem (hx b) (hz b)
    | smul c x _ hx =>
      intro b
      rw [smul_smul]; exact hx _
  simpa using key 1

private theorem div_of_idHat {𝔟 : Ideal (𝓞 D.F)} {c : 𝓞 D.F} {N : ℕ} (h : ∀ x ∈ 𝔟, ∃ z : 𝓞 D.F, c * x = N * z)
    {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ idHat D 𝔟) : ∃ w ∈ LaHat D, mulF D c v = N • w := by
  induction hv using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hu
    obtain ⟨z, hz⟩ := h x hx
    exact ⟨mulF D z w, mulF_mem z hw, by rw [← mulF_mul, hz, mulF_mul, mulF_nat]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, ew⟩ := hx
    obtain ⟨w', hw', ew'⟩ := hy
    exact ⟨w + w', add_mem hw hw', by rw [map_add (f := _), ew, ew', smul_add]⟩
  | neg x _ hx =>
    obtain ⟨w, hw, ew⟩ := hx
    exact ⟨-w, neg_mem hw, by rw [map_neg, ew, smul_neg]⟩

private theorem crt_part (L : Link D G) (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)) (s t : 𝓞 D.F) (ht : t ∈ 𝔞)
    (e : (N₀ : 𝓞 D.F) * s + t = 1) (g : G.GAf) :
    CongId L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) g ↔ L.CongOne N₀ g ∧ CongId L 𝔞 g := by
  have hN : (N₀ : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} := Ideal.mem_span_singleton_self _
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v hv => idHat_mono Ideal.mul_le_right (h v hv)⟩
    obtain ⟨w, hw, ew⟩ := div_of_idHat (c := 1) (N := N₀) (fun x hx => by
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.mul_le_left hx)
      exact ⟨z, by rw [_root_.one_mul, ← hz, _root_.mul_comm]⟩) (h v hv)
    rw [mulF_one] at ew
    refine ⟨w, hw, ?_⟩
    rw [← ew]; abel
  · rintro ⟨h1, h2⟩ v hv
    obtain ⟨w, hw, ew⟩ := h1 v hv
    have hu : L.actG g v - v = N₀ • w := by rw [ew]; abel
    have hu2 := h2 v hv
    have dec : L.actG g v - v = mulF D ((N₀ : 𝓞 D.F) * s) (L.actG g v - v) + mulF D t (L.actG g v - v) := by
      rw [← mulF_add, e, mulF_one]
    rw [dec]
    refine add_mem (mulF_mem_idHat_mul (Ideal.mul_mem_right _ _ hN) hu2) ?_
    rw [hu, ← mulF_nat, ← mulF_mul, _root_.mul_comm t]
    exact mem_idHat (Ideal.mul_mem_mul hN ht) hw

private theorem bezout {q N₀ : ℕ} {r : ℤ} {𝔞 : Ideal (𝓞 D.F)} (hc : N₀.Coprime q) (e : ℕ) (he : uId D q r ^ e ≤ 𝔞) :
    ∃ s t : 𝓞 D.F, t ∈ 𝔞 ∧ (N₀ : 𝓞 D.F) * s + t = 1 := by
  have hq : ((q : 𝓞 D.F)) ^ e ∈ 𝔞 :=
    he (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_insert _ _)) e)
  have hc' : IsCoprime (N₀ : ℤ) ((q ^ e : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e hc)
  obtain ⟨u, v, huv⟩ := hc'
  refine ⟨(u : 𝓞 D.F), (v : 𝓞 D.F) * (q : 𝓞 D.F) ^ e, Ideal.mul_mem_left _ _ hq, ?_⟩
  have := congrArg (Int.cast : ℤ → 𝓞 D.F) huv
  push_cast at this
  rw [← this]; ring

private theorem gen_part (hLG : LatGen) (L : Link D G) (𝔞 : Ideal (𝓞 D.F)) (g : G.GAf) (hg : Integ L g)
    (a : 𝓞 D.F) (N : ℕ) (hN : 0 < N) (hNp : N.Coprime p) (hgen : IsGen a N 𝔞) :
    CongId L 𝔞 g ↔ ∀ y : D.La, ∃ v ∈ LaHat D,
      L.actG g (inAf D (algebraMap (𝓞 D.F) D.O a • y)) = inAf D (algebraMap (𝓞 D.F) D.O a • y) + N • v := by
  have hNa : (N : 𝓞 D.F) ∈ 𝔞 := by
    have : (N : 𝓞 D.F) ∈ (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 := by
      rw [show (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 = _ from hgen]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_right this
  have hax : ∀ x ∈ 𝔞, ∃ z : 𝓞 D.F, a * x = N * z := fun x hx => by
    have : a * x ∈ Ideal.span {(N : 𝓞 D.F)} := by
      rw [← show (Ideal.span {a} ⊔ Ideal.span {(N : 𝓞 D.F)}) * 𝔞 = _ from hgen]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) hx
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨z, by rw [← hz, _root_.mul_comm]⟩
  constructor
  · intro h y
    obtain ⟨w, hw, ew⟩ := div_of_idHat hax (h _ (inAf_mem' y))
    refine ⟨w, hw, ?_⟩
    rw [map_sub, ← actG_mulF, mulF_inAf] at ew
    rw [← ew]; abel
  · intro h
    have step1 : ∀ v ∈ LaHat D, ∃ w ∈ LaHat D, mulF D a (L.actG g v - v) = N • w := fun v hv => by
      obtain ⟨x, w', hw', rfl⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N hN hNp v hv
      obtain ⟨v₁, hv₁, e₁⟩ := h x
      refine ⟨v₁ + mulF D a (L.actG g w' - w'), add_mem hv₁ (mulF_mem a (sub_mem (hg _ hw') hw')), ?_⟩
      have e₂ : mulF D a (L.actG g (inAf D x) - inAf D x) = N • v₁ := by
        rw [map_sub, ← actG_mulF, mulF_inAf, e₁]; abel
      have e₃ : L.actG g (inAf D x + N • w') - (inAf D x + N • w') =
          (L.actG g (inAf D x) - inAf D x) + N • (L.actG g w' - w') := by
        rw [map_add (f := _), map_nsmul, smul_sub]; abel
      rw [e₃, map_add (f := _), e₂, map_nsmul, smul_add]
    intro v hv
    have hu : L.actG g v - v ∈ LaHat D := sub_mem (hg v hv) hv
    obtain ⟨w₁, hw₁, e₁⟩ := step1 v hv
    obtain ⟨y, w, hw, e₂⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N hN hNp _ hu
    have hdvd : ∃ u : D.La, algebraMap (𝓞 D.F) D.O a • y = N • u := by
      refine GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul p D N hN hNp (GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP p N hN hNp) _ ⟨w₁ - mulF D a w, sub_mem hw₁ (mulF_mem a hw), ?_⟩
      rw [e₂, map_add (f := _), mulF_inAf, map_nsmul] at e₁
      rw [smul_sub, ← e₁]; abel
    have hy : y ∈ wSub D 𝔞 1 := ((hLG p D a N 𝔞 hN hgen).1 y).1 hdvd
    rw [e₂]
    refine add_mem (wSub_inAf hy) ?_
    rw [← mulF_nat]
    exact mem_idHat hNa hw

end UpperTheory.Gal.Int.Geo.CRT

open UpperTheory.Gal.Int.Geo.CRT in
theorem UpperTheory.congruenceCRT_of_latticeGen :
    LatGen → CongCRT := by
  intro hLG p _ D G L q r N₀ 𝔞 hc ⟨e, he⟩ g hg
  obtain ⟨s, t, ht, est⟩ := bezout hc e he
  exact ⟨crt_part L N₀ 𝔞 s t ht est g, fun a N hN hNp hgen => gen_part hLG L 𝔞 g hg a N hN hNp hgen⟩

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsNumberFieldPointOfGeneric
section
open UpperTheory.Gal.Int.Geo
open NumberField

private lemma natDvd_of_eq_mul {F : Type} [Field F] [NumberField F] {n m : ℕ} {x : 𝓞 F}
    (h : (n : 𝓞 F) * x = (m : 𝓞 F)) : n ∣ m := by
  have hd : Module.finrank ℤ (𝓞 F) ≠ 0 := Module.finrank_pos.ne'
  have hn := congrArg (Algebra.norm ℤ) h
  have e : ∀ k : ℕ, (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := fun k => by simp
  rw [map_mul, e n, e m, Algebra.norm_algebraMap, Algebra.norm_algebraMap] at hn
  have hdvd : (n : ℤ) ^ Module.finrank ℤ (𝓞 F) ∣ (m : ℤ) ^ Module.finrank ℤ (𝓞 F) :=
    ⟨_, hn.symm⟩
  exact Int.natCast_dvd_natCast.1 ((Int.pow_dvd_pow_iff hd).1 hdvd)

theorem UpperTheory.exists_number_field_point_of_generic :
    GenEx → NumEx := by
  intro hG p _ D E _ _ gb w q _ r 𝔴 𝔫 S N hN
  refine ⟨fun hmem => ?_, fun c a t h => ?_⟩
  · rw [S.lev] at hmem
    obtain ⟨x, hx, hxe⟩ := Ideal.mem_span_singleton_mul.1 hmem
    have hNa : (N : 𝓞 D.F) ∈ S.𝔞 := hxe ▸ Ideal.mul_mem_left _ _ hx
    obtain ⟨a, ha⟩ := (hG (𝓞 D.F) S.𝔞 N hN).1 hNa
    obtain ⟨c, hc⟩ := natDvd_of_eq_mul hxe
    exact ⟨c, a, hc, ha⟩
  · exact ⟨by rw [h.1, mul_assoc], (hG (𝓞 D.F) S.𝔞 N hN).2 a t h.2⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftExistsOfQuotientLevel
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD TjE KSOKE)
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R'} {N N₀ c : ℕ}

private theorem qcast {o' : GObj gb N s'} {o : Obj b N₀ s} {f g : S' ⟶ S} (e : f = g) (n : QMap o' o f c) :
    ∃ n' : QMap o' o g c, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

private theorem qobj' (hObj : QObj) (β : R →+* R') (hm : Match b gb β) (hN : N = N₀ * c) (h0 : 0 < N) (hc : N₀.Coprime q)
    (o : GObj gb N s') {s₀ : S' ⟶ Sp R} (e : s₀ = s' ≫ spMap β) : ∃ o₀ : Obj b N₀ s₀, Nonempty (QMap o o₀ (𝟙 S') c) := by
  subst e
  exact hObj q D R R' b gb β hm N N₀ c hN h0 hc S' s' o

private theorem sec_hom {X : Scheme.{0}} {A : Over X} (e : 𝟙_ (Over X) ⟶ A) : e.left ≫ A.hom = 𝟙 X := by
  simpa using Over.w e

private theorem sec_lift {X Y : Scheme.{0}} {A : Over X} {B : Over Y} {f : X ⟶ Y} {φ : A.left ⟶ B.left}
    (hc : IsPullback φ A.hom B.hom f) (e : 𝟙_ (Over Y) ⟶ B) : ∃ l : 𝟙_ (Over X) ⟶ A, l.left ≫ φ = f ≫ e.left := by
  refine ⟨Over.homMk (hc.lift (f ≫ e.left) (𝟙 X) (by simp [sec_hom e])) (by simp), ?_⟩
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.hecke_lift_exists_of_quotient_level :
    NumEx → QObj → QComp → QUniq → QLev → TjIsog → TrEta → CongCRT → LiftEx := by
  intro hNumEx hQObj hQComp hQUniq hQLev hTjIsog hTrEta hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N t c a hN't hNum C' C u hu W
  obtain ⟨hNc, hGen⟩ := hNum
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have e0 : (C'.j ≫ S.π) ≫ S.M.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, S.ov, C'.ov]
  obtain ⟨o₁, ⟨n₁⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hN'c hN'pos hcq (T.M N').univ e0
  obtain ⟨o₂, ⟨n₂⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hNc hNpos hcq W.o e0
  obtain ⟨ψ₀, hψ₀, hiso, htj⟩ := hTjIsog p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev i h hTj hInt u hu N' N (c * t) c
    hN'c hNc W _ o₁ o₂ n₁ n₂
  obtain ⟨x1q, hx1q⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ S.Y.univ S.M.univ C'.j S.π).1 C'.m S.mπ
  obtain ⟨x1c, hx1c⟩ := qcast (show C'.j ≫ S.π = 𝟙 _ ≫ (C'.j ≫ S.π) by simp) x1q
  obtain ⟨x1, hx1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ S.M.univ (𝟙 _) (C'.j ≫ S.π)).2.2.1
    inferInstance n₁ x1c
  have hunit : IsUnit ((q : ℕ) : Γ((T.M N').X, ⊤)) := by
    have hqE : IsUnit (q : E) := (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero).isUnit
    simpa using hqE.map (((T.M N').s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom)
  obtain ⟨y₀, ⟨hy₀, m₀, m₁, hm01⟩, -⟩ := Tj.univ _ (C'.j ≫ S.π) o₁ o₂ x1 ψ₀ hunit hiso htj
  obtain ⟨y, hys, hyg⟩ : ∃ y, y ≫ Lj.s = C'.j ∧ y ≫ Lj.g = y₀ :=
    ⟨_, Lj.pb.lift_fst _ _ hy₀.symm, Lj.pb.lift_snd _ _ hy₀.symm⟩
  obtain ⟨n'c, hn'c⟩ := qcast hys.symm C'.m
  obtain ⟨mm, hmm⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o S.Y.univ y Lj.s).2.1 n'c Lj.ms
  obtain ⟨q1, hq1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ Tj.o' (𝟙 _) y₀).1 n₂ m₁
  obtain ⟨q1c, hq1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) q1
  obtain ⟨q2, hq2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' Tj.o' y Lj.g).2.1 q1c Lj.m'
  obtain ⟨q3, hq3⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' S.Y.univ y Lj.t).1 q2 Lj.mt
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨A1, hA1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o Tj.o y Lj.g).1 mm Lj.m₀
  obtain ⟨B1, hB1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ Tj.o (𝟙 _) y₀).1 n₁ m₀
  obtain ⟨B1c, hB1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) B1
  have I1 : mm.φ ≫ Lj.m₀.φ = n₁.φ ≫ m₀.φ := by
    rw [← hA1, ← hB1, ← hB1c]
    exact hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ A1 B1c
  have I2 : mm.φ ≫ Lj.ψ.left = W.ψ.left ≫ q2.φ := by
    apply Lj.m'.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← Lj.sq, reassoc_of% I1, hm01, reassoc_of% hψ₀, ← hq2, hq1c, hq1]
    · simp only [Category.assoc, Over.w, mm.cart.1.w, q2.cart.1.w]
      rw [← Category.assoc (Over.Hom.left W.ψ), Over.w]
  have hIu : Integ L u := integ_of_mem ((hLev u).mp hu).1
  have hCu : CongId L S.𝔞 u := by
    have h1 := ((hLev u).mp hu).2
    rw [S.lev] at h1
    exact ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).1.mp h1).2
  have hCh : CongId L S.𝔞 h := hTj.other S.𝔞 S.sup S.upow
  have hx : ∀ y' : D.La, ∃ v ∈ LaHat D, (L.actG (h * u)) (inAf D ((algebraMap (𝓞 D.F) D.O) a • y')) =
      inAf D ((algebraMap (𝓞 D.F) D.O) a • y') + (N : ℕ) • v := by
    intro y'
    obtain ⟨v₁, hv₁, e₁⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow h hInt).2 a N hNpos N.2.2 hGen).mp hCh y'
    obtain ⟨v₂, hv₂, e₂⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).2 a N hNpos N.2.2 hGen).mp hCu y'
    refine ⟨v₁ + L.actG h v₂, add_mem hv₁ (hInt v₂ hv₂), ?_⟩
    rw [map_mul, Module.End.mul_apply, e₂, map_add (f := _), map_nsmul, e₁, smul_add, add_assoc]
  have I4 : ∀ y' : D.La, ∀ l' : 𝟙_ (Over Lj.Z) ⟶ Lj.o.A, l'.left ≫ Lj.ms.φ = Lj.s ≫ (S.Y.lv y').left →
      ((T.M N').univ.eta (t • ((algebraMap (𝓞 D.F) D.O) a • y'))).left ≫ mm.φ = y ≫ l'.left := by
    intro y' l' hl'
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y' = t • ((algebraMap (𝓞 D.F) D.O) a • y') := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    apply Lj.ms.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← hmm, hn'c, hl', reassoc_of% hys, ← C'.lv, hsm]
    · simp only [Category.assoc]
      rw [mm.cart.1.w, reassoc_of% (sec_hom _), sec_hom l']
      simp
  have I3 : ∀ y' : D.La, (W.o.eta ((algebraMap (𝓞 D.F) D.O) a • y')).left ≫ q3.φ =
      (y ≫ Lj.t) ≫ (S.Y.lv y').left := by
    intro y'
    obtain ⟨l', hl'⟩ := sec_lift Lj.ms.cart.1 (S.Y.lv y')
    have hTE := hTrEta p D G L E gb (h * u) _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ (hx y')
    rw [one_smul] at hTE
    have hlv := Lj.lev y' l' hl'
    rw [Over.comp_left, Category.assoc] at hlv
    rw [← hTE, Over.comp_left, hq3]
    simp only [Category.assoc]
    rw [← reassoc_of% I2, reassoc_of% (I4 y' l' hl'), hlv]
  obtain ⟨l, hlev, hl⟩ := hQLev q _ _ _ _ _ _ _ _ a S.𝔞 hNpos hGen _ _ _ W.o o₂ n₂
  obtain ⟨f₀, -, huniq⟩ := S.Y.rep _ _ o₂ l hlev
  obtain ⟨q3c, hq3c⟩ := qcast (show y ≫ Lj.t = 𝟙 _ ≫ (y ≫ Lj.t) by simp) q3
  obtain ⟨μ2, hμ2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (y ≫ Lj.t)).2.2.1
    inferInstance n₂ q3c
  obtain ⟨qCc, hqCc⟩ := qcast (show W.π ≫ C.j = 𝟙 _ ≫ (W.π ≫ C.j) by simp) qC
  obtain ⟨μ1, hμ1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (W.π ≫ C.j)).2.2.1
    inferInstance n₂ qCc
  have base2 : (y ≫ Lj.t) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    simp only [Category.assoc]
    rw [← S.ov, reassoc_of% Lj.tπ, ← Tj.st, reassoc_of% hyg, reassoc_of% hy₀]
  have base1 : (W.π ≫ C.j) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    rw [e0, Category.assoc, C.ov, reassoc_of% W.ov]
  have eq2 := huniq _ ⟨base2, μ2, fun y' => by
    rw [← hl y', Category.assoc, ← hμ2, hq3c, I3 y']⟩
  have eq1 := huniq _ ⟨base1, μ1, fun y' => by
    rw [← hl y', Category.assoc, ← hμ1, hqCc, hqC, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]⟩
  have yt : y ≫ Lj.t = W.π ≫ C.j := eq2.trans eq1.symm
  obtain ⟨q3y, hq3y⟩ := qcast yt q3
  refine ⟨⟨y, hys, yt, mm, ?_, ?_⟩⟩
  · rw [← hmm, hn'c]
  · rw [reassoc_of% I2, ← hq3, ← hqC, ← hq3y, hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ q3y qC]
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralGeometricGaloisSplitting
section
open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.integralGeometricGalois_splitting : UpperTheory.Gal.Int.Geo.SplitOf := by
  intro W X c _ _ Δ _ a ha h
  refine UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts c c Δ a ha ?_
  intro Ω _ _ x y hy
  obtain ⟨δ, hδ, hu⟩ := h Ω x y hy.symm
  exact ⟨δ, hδ.symm, fun δ' hδ' => hu δ' hδ'.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsogenyClassExistsOfQuotient
section
open UpperTheory.Gal.Int.Geo
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo

theorem UpperTheory.isogeny_class_exists_of_quotient :
    QObj → QComp → QUniq → QLev → ClsEx := by
  intro hObj hComp hUniq hLev q _ D R R' _ _ _ b gb β hM N N₀ c a 𝔞 hN hpos h3 hcop hgen Y X s o
  obtain ⟨o₀, ⟨n⟩⟩ := hObj q D R R' b gb β hM N N₀ c hN hpos hcop X s o
  obtain ⟨l, hl, hln⟩ := hLev q D R R' b gb N N₀ c a 𝔞 hpos hgen X s _ o o₀ n
  obtain ⟨f, ⟨hfs, m, hm⟩, hfu⟩ := Y.rep X _ o₀ l hl
  have key : ∀ (j : X ⟶ Y.X), j ≫ Y.s = s ≫ spMap β → ∀ (k : QMap o Y.univ j c),
      (∀ y : D.La, Over.Hom.left (o.eta ((algebraMap (NumberField.RingOfIntegers D.F) D.O) a • y)) ≫ k.φ =
        j ≫ Over.Hom.left (Y.lv y)) → j = f := by
    intro j hj k hk
    obtain ⟨k', hk'⟩ : ∃ k' : QMap o Y.univ (𝟙 X ≫ j) c, k'.φ = k.φ := by
      rw [Category.id_comp]
      exact ⟨k, rfl⟩
    obtain ⟨m', hm'⟩ :=
      (hComp q D R R' b gb N N₀ c X X Y.X s _ _ o o₀ Y.univ (𝟙 X) j).2.2.1 inferInstance n k'
    apply hfu
    refine ⟨hj, m', fun y => ?_⟩
    rw [← hln y, Category.assoc, ← hm', hk']
    exact hk y
  obtain ⟨n', hn'⟩ := (hComp q D R R' b gb N N₀ c X X Y.X s _ _ o o₀ Y.univ (𝟙 X) f).1 n m
  refine ⟨⟨⟨𝟙 X ≫ f, by rw [Category.id_comp, hfs], n', fun y => ?_⟩⟩, ?_⟩
  · rw [hn', ← Category.assoc, hln y, hm y, Category.id_comp]
  · intro C C'
    obtain ⟨j, ov, k, hk⟩ := C
    obtain ⟨j', ov', k', hk'⟩ := C'
    have e1 := key j ov k hk
    have e2 := key j' ov' k' hk'
    subst e1
    subst e2
    exact ⟨rfl, hUniq q D R R' b gb N N₀ c h3 hcop X Y.X s Y.s o Y.univ _ k k'⟩
end

