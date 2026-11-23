module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilRepRationalPointsThetaFunctionsFock
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.AhFrameFactorEqNegOnePowRiemannForm
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedMatrixIffFrameCoordinatesOfInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.InertLocFrame.xm_bij_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (L : Type) [Field L] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L) (z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
        At (evFin F v) z ↔ ∃ x, GlobalTheory.InertLocFrame.xm ι PV PW x = z := by
  intro F E _ _ _ _ _ v n d L _ ι _ him _ PV PW z
  constructor
  · intro hz
    have hent : ∀ i j, ∃ y, ι y = z i j := fun i j => (him (z i j)).1 (fun u hu => by
        have := congrFun (congrFun (hz u hu) i) j
        simpa using this)
    choose y hy using hent
    refine ⟨(((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.of y * ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L)ᵀ)ᵀ, ?_⟩
    rw [GlobalTheory.InertLocFrame.xm_apply, Matrix.transpose_transpose]
    have h1 : (PV : Matrix (Fin n) (Fin n) L) * ((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv PV
    have h2 : (((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L))ᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have h3 : (PV : Matrix (Fin n) (Fin n) L) * (((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.of y *
        ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L)ᵀ) * (PW : Matrix (Fin d) (Fin d) L)ᵀ = Matrix.of y := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
    rw [h3]
    ext i j
    simp [hy]
  · rintro ⟨x, rfl⟩ u hu
    ext i j
    rw [Matrix.smul_apply, GlobalTheory.InertLocFrame.xm_apply, Matrix.map_apply]
    exact (him _).2 ⟨_, rfl⟩ u hu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystem
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.SymCols

variable {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K A)

theorem word_const (l : Fin N → K) (n : ℕ) : word mul (fun _ : Fin n => l) = mul l ^ n := by
  simp [word, List.ofFn_const, List.prod_replicate]

theorem join_fun {D : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K) (b : Fin (D + 1)) :
    (fun k => join s l (b, k)) = Fin.lastCases (motive := fun _ => Fin N → K) l s b := by
  induction b using Fin.lastCases with
  | last => funext k; simp [join]
  | cast i => funext k; simp [join]

theorem word_join (hc : ∀ u v, mul u * mul v = mul v * mul u) {D t : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K)
    (β : Fin t → Fin (D + 1)) (α : Fin D →₀ ℕ)
    (hα : ∀ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card = α i) :
    word mul (fun q k => join s l (β q, k)) =
      pw mul s α * mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card := by
  classical
  let P := Submonoid.closure (Set.range mul)
  letI : CommMonoid P := { P.toMonoid with
    mul_comm := by
      intro ⟨x, hx⟩ ⟨y, hy⟩
      apply Subtype.ext
      exact Submonoid.closure_induction₂
        (by rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact hc u v)
        (by simp) (by simp)
        (by
          intro x y z _ _ _ h1 h2
          change x * z = z * x at h1
          change y * z = z * y at h2
          change (x * y) * z = z * (x * y)
          rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc])
        (by
          intro x y z _ _ _ h1 h2
          change z * x = x * z at h1
          change z * y = y * z at h2
          change z * (x * y) = (x * y) * z
          rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]) hx hy }
  let G : (Fin N → K) → P := fun u => ⟨mul u, Submonoid.subset_closure ⟨u, rfl⟩⟩
  let φ : P →* Module.End K A := P.subtype
  have key : ∀ {n : ℕ} (f : Fin n → P), (List.ofFn fun i => φ (f i)).prod = φ (∏ i, f i) := by
    intro n f
    rw [← List.prod_ofFn]
    change (List.ofFn (φ ∘ f)).prod = _
    rw [← List.map_ofFn, map_list_prod]
  let H : Fin (D + 1) → Fin N → K := Fin.lastCases (motive := fun _ => Fin N → K) l s
  have h1 : word mul (fun q k => join s l (β q, k)) = φ (∏ q, G (H (β q))) := by
    rw [← key]
    simp only [word, join_fun]
    rfl
  have h2 : pw mul s α = φ (∏ i, G (s i) ^ α i) := by
    rw [← key]
    simp only [pw, map_pow]
    rfl
  rw [h1, h2, show mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card = φ (G l ^ (Finset.univ.filter fun q => β q = Fin.last D).card) from (map_pow φ (G l) _).symm, ← map_mul]
  congr 1
  rw [Finset.prod_comp (fun b => G (H b)) β]
  rw [Finset.prod_subset (Finset.subset_univ _)]
  · rw [Fin.prod_univ_castSucc]
    apply congrArg₂ (fun (x y : P) => x * y)
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [H, hα]
    · simp [H]
  · intro b _ hb
    have : (Finset.univ.filter fun q => β q = b).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q _ hq
      exact hb (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩)
    rw [this]
    exact pow_zero _

theorem card_fibers {D t : ℕ} (β : Fin t → Fin (D + 1)) :
    ∑ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card +
      (Finset.univ.filter fun q => β q = Fin.last D).card = t := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := β)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  rw [Fin.sum_univ_castSucc] at this
  exact this.symm

end GlobalTheory.HSShort.SymCols

open GlobalTheory.HSShort.SymCols in
theorem GlobalTheory.HSShort.symbols_of_columns : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → ∀ l : Fin S.N → E, (∀ (a : Fin (S.T - S.D)) (α : MonoDeg (Fin S.D) a) (p : Fin δ), ∃ h : word Φ.mul (fun q k => join s l ((col (ix (⟨a, α⟩, p))).β q, k)) (Φ.ι (col (ix (⟨a, α⟩, p))).x) ∈ Φ.U a, ∀ α' p', Φ.sym a ⟨_, h⟩ (α', p') = if α'.1 = α.1 then (∑ k, l k * Φ.y p' k) ^ (S.T - a) * Φ.res (Φ.ι (m p)) p' else 0) ∧ ∀ k, k ∉ Set.range ix → (col k).j = S.D → word Φ.mul (fun q j => join s l ((col k).β q, j)) (Φ.ι (col k).x) ∈ Φ.U (S.T - S.D) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d col m ix hsh l
  refine ⟨fun a α p => ?_, fun k hk hj => ?_⟩
  · set κ := col (ix (⟨a, α⟩, p)) with hκ
    have hj : κ.j = 0 := hsh.x_j _
    have hx : (κ.x : A) = m p := hsh.x_vec _
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => κ.β q = i.castSucc).card = α.1 i := hsh.x_type _
    have ht : κ.t = S.T := by have := κ.add; omega
    have hdeg : ∑ i : Fin S.D, α.1 i = a := by rw [← Finsupp.degree_eq_sum]; exact α.2
    have hlast : (Finset.univ.filter fun q => κ.β q = Fin.last S.D).card = S.T - a := by
      have := card_fibers κ.β
      simp only [htype, hdeg] at this
      omega
    have heq : word Φ.mul (fun q k => join s l (κ.β q, k)) (Φ.ι κ.x) =
        pw Φ.mul s α.1 (word Φ.mul (fun _ : Fin (S.T - a) => l) (Φ.ι (m p))) := by
      rw [word_join Φ.mul Φ.comm s l κ.β α.1 htype, hlast, word_const, Module.End.mul_apply, hx]
    obtain ⟨h, hsym⟩ := Φ.mono a (by omega) α (fun _ => l) (Φ.ι (m p))
      (Submodule.subset_span ⟨(m p : A), (m p).2, rfl⟩)
    rw [heq]
    refine ⟨h, fun α' p' => ?_⟩
    rw [hsym]
    simp
  · have hrest := hsh.rest k hk
    have hno : ∀ q, (col k).β q ≠ Fin.last S.D := by
      rcases hrest with h | h
      · exact h.2
      · have := hS.le_T; omega
    classical
    let α : Fin S.D →₀ ℕ := Finsupp.equivFunOnFinite.symm
      (fun i => (Finset.univ.filter fun q => (col k).β q = i.castSucc).card)
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => (col k).β q = i.castSucc).card = α i := fun i => rfl
    have h0 : (Finset.univ.filter fun q => (col k).β q = Fin.last S.D).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun q _ => hno q
    have ht : (col k).t = S.T - S.D := by have := (col k).add; omega
    have hdeg : α.degree = S.T - S.D := by
      rw [Finsupp.degree_eq_sum]
      have := card_fibers (col k).β
      rw [h0] at this
      simpa [α, ht] using this
    rw [word_join Φ.mul Φ.comm s l (col k).β α htype, h0, pow_zero, mul_one, Φ.div]
    refine Submodule.mem_iSup_of_mem ⟨α, hdeg⟩ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨((col k).x : A), ?_, rfl⟩))
    have key : ∀ (j : ℕ) (x : S.V j), j = S.D → (x : A) ∈ S.V S.D := by rintro j x rfl; exact x.2
    exact key _ _ hj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertVacIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_eq_map_compFin (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.EmbChart.atPlace v 1 • a =
      TensorProduct.map (GlobalTheory.EmbChart.atPlace v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem smul_eq_zero_of_compFin (v : Pl (F := F)) {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (h : compFin F E v a = 0) :
    GlobalTheory.EmbChart.atPlace v 1 • a = 0 := by
  rw [smul_eq_map_compFin, h, map_zero]

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    compFin F E v (cA σ a) =
      Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b => simp [cA, compFin, Algebra.TensorProduct.map_tmul]

theorem self_eq_smul_of_at {n d : ℕ} (v : Pl (F := F)) {u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (h : At (evFin F v) u) :
    u = GlobalTheory.EmbChart.atPlace v 1 • u := by
  have h1 := h (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem hTens_eq_sum {α β : Type} [Fintype α] [Fintype β] (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →ₐ[AF F] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (x y : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symp_eq_zero_of_lagAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d m : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (W : Spc F E d) (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    GlobalTheory.InertVacLag.IsLagrAt σ W v C → ∀ (ξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    u ∈ GlobalTheory.InertVacLag.lagAt v C → u' ∈ GlobalTheory.InertVacLag.lagAt v C →
    symp (cA σ) ξ (incM F JX) (incM F W.J) u u' = 0 := by
  intro F E _ _ _ _ _ σ n d m JX W v C hL ξ u u' hu hu'
  obtain ⟨hat, z, rfl⟩ := hu
  obtain ⟨-, z', rfl⟩ := hu'
  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v)
  set P := Cᵀ * incM F W.J * C.map (cA σ) with hP
  have hPv : P.map (compFin F E v) = 0 := by
    have h1 := hL.1
    rw [hP, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    convert h1 using 2
    · congr 1
    · ext i j
      simp only [Matrix.map_apply]
      exact compFin_cA σ v (C i j)
  have heP : e • P = 0 := by
    ext p q
    rw [Matrix.smul_apply, Matrix.zero_apply]
    apply smul_eq_zero_of_compFin
    have := congrArg (fun M => M p q) hPv
    simpa using this
  have hM : z * Cᵀ * incM F W.J * ((z' * Cᵀ).map (cA σ))ᵀ = 0 := by
    rw [self_eq_smul_of_at v hat]
    have hmap : (z' * Cᵀ).map (cA σ) = z'.map (cA σ) * Cᵀ.map (cA σ) :=
      Matrix.map_mul (f := (cA σ).toRingHom)
    rw [hmap, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    rw [Matrix.smul_mul, Matrix.smul_mul]
    have : z * Cᵀ * incM F W.J * (C.map (cA σ) * (z'.map (cA σ))ᵀ) = z * P * (z'.map (cA σ))ᵀ := by
      rw [hP]; simp only [Matrix.mul_assoc]
    rw [this, ← Matrix.smul_mul, ← Matrix.mul_smul, heP, Matrix.mul_zero, Matrix.zero_mul]
  rw [symp, hTens_eq_sum, hM]
  simp

end GlobalTheory.InertVacIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorCompare

section Theta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.Ker GlobalTheory.Ker.HatLat GlobalTheory.ThetaSpace
open scoped TensorProduct

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ}

theorem parts_eInf_smul (a : AE D) :
    finPart D (FinTranslate.eInf D • a) = 0 ∧ infPart D (a - FinTranslate.eInf D • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero, sub_zero, map_zero, and_self]
  | add a b ha hb =>
    refine ⟨by rw [smul_add, RingHom.map_add (f := _), ha.1, hb.1, add_zero], ?_⟩
    rw [smul_add, add_sub_add_comm, RingHom.map_add (f := _), ha.2, hb.2, add_zero]
  | tmul a x =>
    rw [TensorProduct.smul_tmul', ← TensorProduct.sub_tmul]
    constructor
    · show (sndA D.host.F (FinTranslate.eInf D • a)) ⊗ₜ[D.host.F] x = 0
      rw [show sndA D.host.F (FinTranslate.eInf D • a) = 0 from zero_mul _, TensorProduct.zero_tmul]
    · show (fstA D.host.F (a - FinTranslate.eInf D • a)) ⊗ₜ[D.host.F] x = 0
      rw [show fstA D.host.F (a - FinTranslate.eInf D • a) = 0 from
        (show a.1 - 1 * a.1 = 0 by rw [one_mul, sub_self]), TensorProduct.zero_tmul]

theorem exists_fin_add_real (w : WO S T) : ∃ u v, IsFinPt u ∧ IsRealPt v ∧ w = u + v :=
  ⟨w - FinTranslate.eInf D • w, FinTranslate.eInf D • w, Matrix.ext fun i j => (parts_eInf_smul (w i j)).2,
    Matrix.ext fun i j => (parts_eInf_smul (w i j)).1, (sub_add_cancel _ _).symm⟩

theorem isTheta_heisO (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    IsThetaFunO ψ S T (heisO ψ S T w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  have h := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 (WeilVacMove.isTheta_heisO_real hψ hv hf) hu
  rwa [WeilVacMove.heisO_heisO, (WeilVacMove.symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one,
    one_smul] at h

theorem theta_eq_zero_of_real {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : ∀ w, IsRealPt w → f w = 0) :
    f = 0 := by
  have hΛ := stdL_full D.host.E S.rank
  have hL := stdL_full D.host.E T.rank
  have hO : ∀ c : 𝓞 D.host.F, ∀ y ∈ GlobalTheory.SW.tens (GlobalTheory.SW.stdL D.host.E S.rank) (GlobalTheory.SW.stdL D.host.E T.rank),
      (c : D.host.F) • y ∈ GlobalTheory.SW.tens (GlobalTheory.SW.stdL D.host.E S.rank) (GlobalTheory.SW.stdL D.host.E T.rank) := fun c y hy =>
    smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hy
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := exists_nsmul_mem_open (F := D.host.F) (tens_fg _ _ hΛ.1 hL.1) U hU
  funext w
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  obtain ⟨y, hy⟩ := exists_rat (F := D.host.F) (tens_den _ _ hΛ.2 hL.2) hu
  obtain ⟨y', -, u', hu', e⟩ := exists_mod hO hN hy
  have hfin : IsFinPt (S := S) (T := T) (N • u') := isFinPt_nsmul (inf_eq_zero_of_mem (F := D.host.F) hu') N
  have hr0 : IsRealPt (ratW T S (y + y')ᵀ - finW S T (y + y')) := by
    funext a k
    show finPart D (incA D ((y + y') k a) - finW S T (y + y') a k) = 0
    rw [RingHom.map_sub]
    exact sub_eq_zero.2 rfl
  have hr := isRealPt_sub hv hr0
  have e0 : finW S T (y + y') = fT D.host.F 1 y + fT D.host.F 1 y' := (fT D.host.F 1).map_add y y'
  have e1 : u + v = ratW T S (y + y')ᵀ + ((v - (ratW T S (y + y')ᵀ - finW S T (y + y'))) + N • u') := by
    rw [e0, sub_eq_iff_eq_add.1 e]
    abel
  have e2 := congrFun (hl _ (hNU u' hu') hfin) (v - (ratW T S (y + y')ᵀ - finW S T (y + y')))
  rw [h0 _ hr] at e2
  unfold heisO at e2
  rw [(WeilVacMove.symplOH_fin_real S T _ _ hfin hr).2, AddChar.map_zero_eq_one, one_mul] at e2
  rw [e1, hf.quasi, e2, mul_zero, Pi.zero_apply]

end Theta

section Can

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

end Can

section Const

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct

variable {D : D7}

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Const

end GlobalTheory.TwistFactorCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormMapSurjective
section
open NumberField

noncomputable section

namespace GlobalTheory.TraceDual

def traceFormMap (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] Module.Dual ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun Y X => -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i))
    (fun Y₁ Y₂ X => by simp [mul_add, Finset.sum_add_distrib]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])
    (fun Y X₁ X₂ => by simp [add_mul, Finset.sum_add_distrib, mul_add]; ring)
    (fun c Y X => by simp [Finset.mul_sum, mul_left_comm])

theorem traceFormMap_apply (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (Y X : κ → mixedEmbedding.mixedSpace F) :
    traceFormMap F κ Y X = -(2 * Real.pi) *
      ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := rfl

theorem traceFormMap_injective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Injective (traceFormMap F κ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Y hY
  have h0 := LinearMap.congr_fun hY (fun i => GlobalTheory.VacLn.TrNondeg.conjM (Y i))
  rw [traceFormMap_apply, LinearMap.zero_apply] at h0
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (neg_eq_zero.1 h) hpi
    · exact h
  have hnn : ∀ i, 0 ≤ Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (GlobalTheory.VacLn.TrNondeg.conjM (Y i) * Y i) := by
    intro i
    rw [GlobalTheory.VacLn.TrNondeg.trace_conjM_mul]
    exact add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
      (Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have e := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h1
  funext i
  exact GlobalTheory.VacLn.TrNondeg.eq_zero_of_trace_conjM_mul _ (e i (Finset.mem_univ _))

theorem traceFormMap_surjective (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Function.Surjective (traceFormMap F κ) := by
  have h := Subspace.dual_finrank_eq (K := ℝ) (V := κ → mixedEmbedding.mixedSpace F)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h.symm).1
    (traceFormMap_injective F κ)

theorem exists_trace_rep : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ), ∃ Y : κ → mixedEmbedding.mixedSpace F,
      ∀ X, L X = -(2 * Real.pi) * ∑ i, Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X i * Y i) := by
  intro F _ _ κ _ L
  obtain ⟨Y, hY⟩ := traceFormMap_surjective F κ L.toLinearMap
  exact ⟨Y, fun X => by rw [← traceFormMap_apply, hY]; rfl⟩

end GlobalTheory.TraceDual
end
end

