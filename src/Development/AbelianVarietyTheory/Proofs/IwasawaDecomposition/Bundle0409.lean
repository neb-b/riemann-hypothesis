module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Formalism.LocalToGlobal.Columns.Bundle0046
public import Formalism.LocalToGlobal.Columns.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceSupportLevelStandardCoordinates
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLevelCharacterFiniteOrder
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem lamExp_of_princ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (lam : ↥H →* Kˣ)
    (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ H, lam ⟨g, h⟩ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : ↥H, lam x ^ m = 1 := by
  set L : Subgroup ↥(GLint E n P) := lam.ker.map H.subtype with hL
  have hfin : Finite (↥(GLint E n P) ⧸ L) := tfFinite_of_princ P N hN L fun g hg =>
    ⟨⟨g, (hH g hg).choose⟩, (hH g hg).choose_spec, rfl⟩
  have hLi : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hrel := Subgroup.relIndex_mul_index hLH
  have hsub : L.subgroupOf H = lam.ker := Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hki : lam.ker.index ≠ 0 := by
    intro h0
    apply hLi
    rw [← hrel, Subgroup.relIndex, hsub, h0, zero_mul]
  refine ⟨lam.ker.index, Nat.pos_of_ne_zero hki, fun x => ?_⟩
  have := Subgroup.pow_index_mem lam.ker x
  rw [MonoidHom.mem_ker, map_pow] at this
  exact this

theorem qbLoc_chr_exp {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {Q : Finset (Pl E)} (Θ : LevQFam E K n Q) (hQ : ∀ P : Q, conjPrime₂ P.1 ≠ P.1) (hΘ : ThetaOpen Θ) (P : Q) : ∃ m : ℕ, 0 < m ∧ ∀ k, (qbLoc hc Θ hQ hΘ).chr P k ^ m = 1 := by
  obtain ⟨N, hN, hH⟩ := hΘ P
  obtain ⟨m, hm, hx⟩ := lamExp_of_princ P.1 N hN (Θ P).H (Θ P).lam hH
  exact ⟨m, hm, fun k => hx _⟩

end GlobalTheory.Mem.Col2.ChEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenLevelCutByCosetStabiliser
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section CutOpen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

omit [StarRing E] in
theorem intAt_iff_val_le_one {P : HeightOneSpectrum (𝓞 E)} {a : E} : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  intro h
  obtain ⟨r, s, hs⟩ := P.exists_primeCompl_mul_eq_of_integer a h
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hs⟩

theorem mem_stdAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (x : Sp E n) :
    x ∈ stdAt E n P ↔ ∀ i, P.valuation E (x i) ≤ 1 := by
  rw [ciMem_stdAt]
  exact forall_congr' fun _ => intAt_iff_val_le_one

theorem lqPrinc_mono {P : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (h : N ≤ N') {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : lqPrinc P N' g) : lqPrinc P N g := by
  intro i j
  refine (hg i j).trans ?_
  change WithZero.exp (-(N' : ℤ)) ≤ WithZero.exp (-(N : ℤ))
  rw [WithZero.exp_le_exp]
  omega

theorem smul_sub_mem_of_princ {P : HeightOneSpectrum (𝓞 E)} {N a : ℕ} (g : ↥(GLint E n P))
    (hg : lqPrinc P (N + a) (g : Sp E n ≃ₗ[E] Sp E n)) {c : E} {z : Sp E n}
    (ha : ∀ j, P.valuation E (c⁻¹ * z j) ≤ WithZero.exp (a : ℤ)) {x : Sp E n}
    (hx : c⁻¹ • (x - z) ∈ stdAt E n P) : c⁻¹ • ((g : Sp E n ≃ₗ[E] Sp E n) x - z) ∈ stdAt E n P := by
  set f : Sp E n ≃ₗ[E] Sp E n := g.1 with hf
  have hgw : f (c⁻¹ • (x - z)) ∈ stdAt E n P := (g.2 _).2 hx
  have hsplit : c⁻¹ • (f x - z) = f (c⁻¹ • (x - z)) + c⁻¹ • (f z - z) := by
    rw [map_smul, map_sub, smul_sub, smul_sub, smul_sub]
    abel
  rw [hsplit]
  refine (stdAt E n P).add_mem hgw ?_
  rw [mem_stdAt_iff_val]
  intro i
  have hfz : f z - z = (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) *ᵥ z := by
    rw [Matrix.sub_mulVec, LinearMap.toMatrix'_mulVec, Matrix.one_mulVec]
    rfl
  have e : (c⁻¹ • (f z - z)) i = ∑ j, (LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) i j * (c⁻¹ * z j) := by
    rw [hfz, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  calc P.valuation E ((LinearMap.toMatrix' (f : Sp E n →ₗ[E] Sp E n) - 1) i j) * P.valuation E (c⁻¹ * z j)
      ≤ WithZero.exp (-((N + a : ℕ) : ℤ)) * WithZero.exp (a : ℤ) := mul_le_mul' (hg i j) (ha j)
    _ = WithZero.exp (-(N : ℤ)) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring
    _ ≤ 1 := by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega

theorem thetaOpen_cutQ {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q) (hΘ : ThetaOpen Θ)
    (C : ∀ P : Q, Set (Sp E n))
    (hC : ∀ P : Q, C P = ∅ ∨ ∃ (z : Sp E n) (c : E), c ≠ 0 ∧ C P = {x | c⁻¹ • (x - z) ∈ stdAt E n P.1}) :
    ThetaOpen (cutQ Θ C) := by
  intro P
  obtain ⟨N, hN, hT⟩ := hΘ P
  have hstab : ∃ N' : ℕ, N ≤ N' ∧ ∀ g : ↥(GLint E n P.1), lqPrinc P.1 N' (g : Sp E n ≃ₗ[E] Sp E n) →
      g ∈ frStab P.1 (C P) := by
    rcases hC P with h | ⟨z, c, _, h⟩
    · refine ⟨N, le_rfl, fun g _ => ?_⟩
      rw [mem_frStab, h]
      intro v
      simp
    · obtain ⟨a, ha⟩ := qth_bound P.1 (Matrix.of fun (_ j : Fin n) => c⁻¹ * z j)
      have ha' : ∀ j, P.1.valuation E (c⁻¹ * z j) ≤ WithZero.exp (a : ℤ) := fun j => by
        simpa using ha j j
      refine ⟨N + a, by omega, fun g hg => ?_⟩
      rw [mem_frStab, h]
      intro v
      show c⁻¹ • (g.1 v - z) ∈ stdAt E n P.1 ↔ c⁻¹ • (v - z) ∈ stdAt E n P.1
      constructor
      · intro hv
        have hi := smul_sub_mem_of_princ g⁻¹ (qth_princ_inv P.1 g hg) ha' hv
        have e : ((g⁻¹ : ↥(GLint E n P.1)) : Sp E n ≃ₗ[E] Sp E n) (g.1 v) = v := LinearEquiv.symm_apply_apply g.1 v
        rwa [e] at hi
      · exact smul_sub_mem_of_princ g hg ha'
  obtain ⟨N', hNN, hS⟩ := hstab
  refine ⟨N', by omega, fun g hg => ?_⟩
  obtain ⟨hH, hl⟩ := hT g (lqPrinc_mono hNN hg)
  exact ⟨⟨hH, hS g hg⟩, hl⟩

end CutOpen

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverTypePrimeChosenAndConjStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_over_typePrime_chosen_and_conj : ∀ (D : D7) (k : Fin 2), Function.Injective (Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v))) ∧ (∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal ↔ ∃ i, Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) i = W) ∧ Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
  first | exact @GlobalTheory.PlacesOverG.places_over_g_k | exact GlobalTheory.PlacesOverG.places_over_g_k | (intros; apply GlobalTheory.PlacesOverG.places_over_g_k <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SphericalVectorFixedLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeckeFrob

theorem conjSplit_w (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host) (h : IsConjPl D.host w s.w) :
    (conjSplit s).w = w := by
  have hc : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => by
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact Formalism.HC.HostAx.conjE_apply _ _ _
  apply HeightOneSpectrum.ext
  ext x
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [hc]; rfl
  rw [h x _ hy]
  exact Iff.rfl

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n))
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' Dset).Finite) (f f' : GAf L n → W) :
    NG.heckeD J Dset (f + f') = NG.heckeD J Dset f + NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : GAf L n → W,
      Function.support (fun cc : GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dite_eq_right]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply]
  simp only [NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem heckeD_zero (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (Dset : Set (GAf L n)) :
    NG.heckeD J Dset (0 : GAf L n → W) = 0 := by
  funext g
  simp [NG.heckeD]

theorem tN_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (GAf L n)) (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hfin : ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite) {m : ℕ} (F : Fin m → GAf L n → W) :
    NG.tN J s ϖ k (∑ j, F j) = ∑ j, NG.tN J s ϖ k (F j) := by
  classical
  have key : ∀ t : Finset (Fin m), NG.tN J s ϖ k (∑ j ∈ t, F j) = ∑ j ∈ t, NG.tN J s ϖ k (F j) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [NG.tN, heckeD_zero]
    | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      simp only [NG.tN]
      rw [heckeD_add L n J _ hfin, smul_add]
  exact key Finset.univ

theorem prod_eq_vieta (n : ℕ) (β : Multiset ℂ) (hn : Multiset.card β = n) :
    (β.map fun a => X - C a).prod = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : ℂ) ^ k * β.esymm k) * X ^ (n - k) := by
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hn, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [pow_zero, Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.map_singleton,
    Multiset.prod_zero, Multiset.sum_singleton, map_one, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr (by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega) fun k _ => ?_
  rw [map_mul, map_pow, map_neg, map_one, mul_assoc]

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem cls_heq {E : Type} [Field E] [NumberField E] {n : ℕ} {a b : HeightOneSpectrum (𝓞 E)} (h : a = b)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (a.adicCompletion E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (b.adicCompletion E)))
    (he : HEq σ.cl τ.cl) : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls τ) := by
  subst h
  exact heq_of_eq (congrArg (Sigma.mk n) (eq_of_heq he))

end

end GlobalTheory.HeckeFrob

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitLocalLevelFirstFactorReadsComponent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdFirst

theorem qPi_eq_phi_of_adAt : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {Q : Finset (Pl E)} {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (P : Q), conjPrime₂ P.1 ≠ P.1 → ∀ (a : AfE F E) (e : E), adAt F P.1 a = algebraMap E _ e → qPi q P a = q.phi P e := by
  intro F E K _ _ _ _ _ _ _ hc n _ Q Θ q P hP a e he
  have hw : P.1.under (𝓞 F) = qv F P.1 := HeightOneSpectrum.ext rfl
  set ψ := GlobalTheory.Mem.Dil.psi (qv F P.1) P.1 hw with hψ
  set sp := q.sp P with hsp

  have hu' : ψ (sp.symm (0, 1)) = 0 := by
    obtain ⟨r, hr, hr'⟩ := exists_mem_notMem (Ne.symm hP)
    have hcr : cO E r ∉ P.1.asIdeal := fun h => hr' ((mem_conjP _ _).2 h)
    obtain ⟨hne, hinv⟩ := qdf_phi_unit q P hcr
    set w := Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) (r : E) with hwdef
    have hws : w = Formalism.UG.sigR hc.sig _ (Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) ((cO E r : 𝓞 E) : E)) := by
      rw [hwdef]
      show _ = Formalism.UG.inclE (F := F) _ (star (star ((r : 𝓞 E) : E)))
      rw [star_star]
    have hw2 : (sp w).2 = q.phi P ((cO E r : 𝓞 E) : E) := by
      rw [hws, hsp, q.sp_sig]
      rfl
    set z := sp.symm (0, ((sp w).2)⁻¹) with hz
    have hzint : z ∈ Formalism.BasicNotions.intV E (qv F P.1) := by
      refine (q.sp_int P z).2 ⟨?_, ?_⟩
      · rw [hz, ← hsp, sp.apply_symm_apply]; exact zero_mem _
      · rw [hz, ← hsp, sp.apply_symm_apply]; show ((sp w).2)⁻¹ ∈ _; rw [hw2]; exact hinv
    have hwz : w * z = sp.symm (0, 1) := by
      apply sp.injective
      rw [map_mul, hz, sp.apply_symm_apply, sp.apply_symm_apply]
      refine Prod.ext (mul_zero _) ?_
      show (sp w).2 * ((sp w).2)⁻¹ = 1
      rw [hw2]
      exact mul_inv_cancel₀ hne
    have hidem : ψ (sp.symm (0, 1)) * ψ (sp.symm (0, 1)) = ψ (sp.symm (0, 1)) := by
      rw [← map_mul, ← map_mul sp.symm]
      simp
    rcases mul_eq_zero.1 (show ψ (sp.symm (0, 1)) * (ψ (sp.symm (0, 1)) - 1) = 0 by rw [mul_sub, hidem, mul_one, sub_self]) with h | h
    · exact h
    · exfalso
      have h1 : ψ (sp.symm (0, 1)) = 1 := sub_eq_zero.1 h
      rw [← hwz, map_mul] at h1
      have hv1 : Valued.v (ψ w) < 1 := by
        rw [hψ, hwdef, GlobalTheory.Mem.Dil.psi_inclE]
        exact GlobalTheory.Mem.Dil.val_lt_one hr
      have hv2 : Valued.v (ψ z) ≤ 1 := (GlobalTheory.Mem.Dil.mem_intV_iff (qv F P.1) z).1 hzint P.1 hw
      have h3 := congrArg Valued.v h1
      rw [map_mul, map_one] at h3
      exact absurd h3 (ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_right' hv2) hv1))
  have hu : ψ (sp.symm (1, 0)) = 1 := by
    have e1 : sp.symm (1, 0) + sp.symm (0, 1) = 1 := by
      rw [← map_add (f := _)]; simp
    have e2 := congrArg ψ e1
    rw [map_add (f := _), hu', add_zero, map_one] at e2
    exact e2

  set x := prV (E := E) (qv F P.1) a - Formalism.UG.inclE (F := F) ((qv F P.1).adicCompletion F) e with hx
  have hψx : ψ x = 0 := by
    rw [hx, map_sub, hψ, GlobalTheory.Mem.Dil.psi_prV, GlobalTheory.Mem.Dil.psi_inclE, he, sub_self]
  have hx1 : (sp x).1 = 0 := by
    by_contra ht
    have hxy : x * sp.symm (((sp x).1)⁻¹, 0) = sp.symm (1, 0) := by
      apply sp.injective
      rw [map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      exact Prod.ext (mul_inv_cancel₀ ht) (mul_zero _)
    have h2 := congrArg ψ hxy
    rw [map_mul, hψx, zero_mul, hu] at h2
    exact zero_ne_one h2
  have e3 : qPi q P a - q.phi P e = (sp x).1 := by
    rw [hx, map_sub]
    rfl
  exact sub_eq_zero.1 (e3.trans hx1)

end GlobalTheory.Mem.Col2.AdFirst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceSupportLevelStandardCoordinatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceSupport_level_standardCoordinates : ∀ (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hI : I.Ok) (hV : ValsIn I) (hL : LevOf X I U L) (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (EA X)) (hF : FrameOK X I U i t A k) (x : (famR X I hX U Xg tr).A.ok t × ℕ) (v : HeightOneSpectrum (𝓞 X.toD7.host.F)) (Pb : HeightOneSpectrum (𝓞 X.toD7.host.E)) (hPb : Formalism.L2.Col.conjPrime₂ Pb = x.1.1.1) (hv : Formalism.L2.Col.IsOver v Pb) (g : Bridge.Gf (Vc X.toD7 i)) (u : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) (hg : castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) ((g : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = A * k * (u : GL (Fin X.B.R.nV) (EA X)) * (A * k)⁻¹),
    ((envL X I hX U Xg tr L cV i t).isLoc x g ↔
      ∀ w : HeightOneSpectrum (𝓞 X.toD7.host.F), w ≠ v →
        Formalism.UG.bc (Formalism.UG.prV (E := X.toD7.host.E) w) (u : GL (Fin X.B.R.nV) (EA X)) = 1) ∧
    ((envL X I hX U Xg tr L cV i t).isLoc x g →
      (g ∈ (envL X I hX U Xg tr L cV i t).lev.J ↔ u ∈ Formalism.L2.Col.mhlKv X.toD7.sp.cm X.B.R.nV v)) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff | exact GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitLoc.loc_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarFiniteAddCharDivNatEqExpTraceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_finiteAddChar_div_nat_eq_exp_trace : ∀ (D : D7) (X : HidaSetting D) (α : 𝓞 D.host.E), star (X.psiEf (divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))))) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ℂ) / ((X.B.g : ℕ) : ℂ)) := by
  first | exact @GlobalTheory.Mem.CharRat.star_psiEf_divN_inclE | exact GlobalTheory.Mem.CharRat.star_psiEf_divN_inclE | (intros; apply GlobalTheory.Mem.CharRat.star_psiEf_divN_inclE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepPointDeterminedByLatticeInvariants
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx


open Classical in
theorem ptDet_cqOf : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    GlobalTheory.Mem.Col2.ChEx.PtDet (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  intro X Pr R sel S mu cst u j hQ hq r r' hfr hb hc
  suffices h2 : r.1.2 = r'.1.2 from Subtype.ext (Prod.ext hfr h2)
  have hd : r.1.1.deco = r'.1.1.deco := congrArg DecoF.deco hfr
  by_cases hj : j + 1 = R.m
  · obtain ⟨y, hy, eY⟩ := (show PtAt R sel mu cst u j from r).mem_ybSet hj
    obtain ⟨y', hy', eY'⟩ := (show PtAt R sel mu cst u j from r').mem_ybSet hj
    have eN : r'.1.1.deco.1.N = r.1.1.deco.1.N := by rw [hd]
    rw [eN] at hy' eY'
    have hyin : y ∈ r.1.2 := by rw [eY, mem_coset, sub_self]; exact zero_mem _
    rw [eY, eY']
    apply coset_eq
    refine (mem_locLat _ _ _ _).2 fun P => ?_
    by_cases hG : P.1 ∈ Pr.vGs
    · rw [if_pos hG, zpow_zero, inv_one, one_smul]
      have hm : r.1.1.deco.1.be ⟨P.1, hG⟩ (((Formalism.L2.Col.qOf P.1 : ℕ) : X.E) • y) ∈ bar r ⟨P.1, hG⟩ := ⟨y, hyin, rfl⟩
      rw [hb] at hm
      obtain ⟨z, hz, ez⟩ := hm
      rw [← hd] at ez
      rw [eY'] at hz
      have hz' := (mem_locLat _ _ _ _).1 (mem_coset.1 hz) P
      rw [if_pos hG, zpow_zero, inv_one, one_smul] at hz'
      have h1 := (mem_locLat _ _ _ _).1 hy P
      have h2 := (mem_locLat _ _ _ _).1 hy' P
      rw [if_pos hG, _root_.zpow_neg_one, inv_inv] at h1 h2
      exact sub_mem_of_be_eq r.1.1.deco.2 ⟨P.1, hG⟩ (hq _ hG) h1 h2 hz' ez
    · rw [if_neg hG, zpow_natCast]
      have hPQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hG
      have hfrP : frsF sel mu r.1.1 P = r.1.1.fr ⟨P.1, hPQ⟩ := by
        unfold frsF
        rw [dite_eq_right hG]
      have hc1 : (r.1.1.fr ⟨P.1, hPQ⟩).symm y ∈ cqOf r ⟨P.1, hPQ⟩ := ⟨y, hyin, by
        show ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (_ - (frsF sel mu r.1.1 P).symm y) ∈ _
        rw [hfrP, sub_self, smul_zero]
        exact zero_mem _⟩
      rw [hc] at hc1
      obtain ⟨y0, hy0, hmem⟩ := hc1
      change ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (_ - (frsF sel mu r'.1.1 P).symm y0) ∈ _ at hmem
      rw [if_neg hG, ← hfr, hfrP] at hmem
      have hA := (r.1.1.2 ⟨P.1, hPQ⟩ _).2 hmem
      change r.1.1.fr ⟨P.1, hPQ⟩ _ ∈ _ at hA
      rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hA
      rw [eY'] at hy0
      have hB := (mem_locLat _ _ _ _).1 (mem_coset.1 hy0) P
      rw [if_neg hG, zpow_natCast] at hB
      have := add_mem hA hB
      rwa [← smul_add, sub_add_sub_cancel] at this
  · have h1 := r.2
    have h1' := r'.2
    rw [ysAt_ys_of_ne sel mu cst hj] at h1 h1'
    exact h1.trans h1'.symm

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnMemberLevelReadAtBasePointStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_member_level_read_at_base_point : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl) (k : Unit → GA B (B.R.N B.R.m)), I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k → let U : Subgroup (GA B (B.R.N B.R.m)) := K.lev.U; let Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E) := K.lev.Lb; let chi : U →* ℂˣ := K.lev.chi; (∀ x ∈ UAd B.sp.cm (B.R.N B.R.m), x ∈ U ↔ (k ())⁻¹ * x * k () ∈ levU B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ((I.Tp a).levG B.R.m).grp) ∧ (∀ (x : U) (z : J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)) (h : ((I.Tp a).levG B.R.m).grp), z.1 = (k ())⁻¹ * x.1 * k () → redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs z = h.1⁻¹ → chi x = Units.map (B.embLL : B.LL →* ℂ) (((I.Tp a).levG B.R.m).chr h)) ∧ ∀ x : Fin (B.R.N B.R.m) → B.host.E ⊗[B.host.F] FiniteAdeleRing (𝓞 B.host.F) B.host.F, x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) Lb ↔ ((k ())⁻¹ : GL (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)).1 *ᵥ x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.kread_member | exact GlobalTheory.Mem.Col2.TopCh.kread_member | (intros; apply GlobalTheory.Mem.Col2.TopCh.kread_member <;> assumption)
end

