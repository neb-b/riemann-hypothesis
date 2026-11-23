module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolic
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedCuspConstantTermVanish
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitaryElementPrescribedBlocks
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExtendByZeroApplyOfNe
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Formalism.FormalDegreeBessel.StatementG
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsKInfEqMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf

open GlobalTheory.Published.AutFin

variable {D : D7}

def kInf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) : GA D V :=
  (Finset.univ.toList.map fun τ => kAt θ V τ (ε τ) (fr τ) (κ τ)).prod

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {ε : D.what₂.Tau → Fin V.rank → Bool}
  {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem kAt_comm (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) (k : Formalism.REAL.KG (ε τ))
    (k' : Formalism.REAL.KG (ε τ')) :
    Commute (kAt θ V τ (ε τ) (fr τ) k) (kAt θ V τ' (ε τ') (fr τ') k') :=
  GlobalTheory.AvgOtherPlace.atTau_comm hθ hne (conj_mem_UH (hfr τ).1 (hfr τ).2 k) (conj_mem_UH (hfr τ').1 (hfr τ').2 k')

theorem exists_kInf_eq_mul (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) (a : D.what₂.Tau) :
    ∃ y : GA D V, ∀ κ' : ∀ τ, Formalism.REAL.KG (ε τ), (∀ τ, τ ≠ a → κ' τ = κ τ) →
      kInf θ V ε fr κ' = y * kAt θ V a (ε a) (fr a) (κ' a) := by
  classical
  let f : (∀ τ, Formalism.REAL.KG (ε τ)) → D.what₂.Tau → GA D V := fun κ τ => kAt θ V τ (ε τ) (fr τ) (κ τ)
  have hperm : (Finset.univ : Finset D.what₂.Tau).toList.Perm (a :: (Finset.univ.erase a).toList) := by
    have := Finset.toList_insert (Finset.notMem_erase a (Finset.univ : Finset D.what₂.Tau))
    rwa [Finset.insert_erase (Finset.mem_univ a)] at this
  refine ⟨((Finset.univ.erase a).toList.map (f κ)).prod, fun κ' hκ' => ?_⟩
  have hpw : ((Finset.univ : Finset D.what₂.Tau).toList.map (f κ')).Pairwise Commute :=
    List.pairwise_map.2 ((Finset.nodup_toList _).imp fun {τ τ'} hne => kAt_comm hθ hfr (Ne.symm hne) _ _)
  have e1 : kInf θ V ε fr κ' = f κ' a * ((Finset.univ.erase a).toList.map (f κ')).prod := by
    rw [kInf, (hperm.map (f κ')).prod_eq' hpw, List.map_cons, List.prod_cons]
  have e2 : (Finset.univ.erase a).toList.map (f κ') = (Finset.univ.erase a).toList.map (f κ) :=
    List.map_congr_left fun τ hτ => by
      simp only [f, hκ' τ (Finset.ne_of_mem_erase (Finset.mem_toList.1 hτ))]
  rw [e1, e2]
  refine (Commute.list_prod_right _ _ fun x hx => ?_).eq
  obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hx
  exact kAt_comm hθ hfr (Finset.ne_of_mem_erase (Finset.mem_toList.1 hτ)) _ _

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCuspFunSlice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice

theorem unip_split : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T →
      ∀ p ∈ unip D.sp.cm.sig V.gram X T, ∃ u ∈ unip D.sp.cm.sig V.gram X S, ∃ l ∈ levi D.sp.cm.sig V.gram X Y S, p = u * l := by
  intro D V m X Y hW S T hST p hpT
  obtain ⟨hcm, hherm⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hherm V
  by_cases hS : S = ∅
  · subst hS
    exact ⟨1, one_mem _, p, by simp, by simp⟩
  obtain ⟨a, ha, ha'⟩ : ∃ a ∈ S, ∀ k ∈ S, k ≤ a := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hP := GlobalTheory.ConstTrans.unip_le_parFlag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T S a hST ha ha' hpT
  have hdec := (GlobalTheory.LeviFlag.levi_decomposition _ _ D.sp.cm.sig hcm _ V.gram hJ (a.val + 1) (initCols X a) (initCols Y a)
    (fun i => (S.filter fun k => k.val < i.val).card)
    (by rw [initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [initCols, initCols, GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]
        exact Matrix.submatrix_one _ (Fin.castLE_injective a.2))).1
  obtain ⟨u, hu, l, hl, rfl, -⟩ := hdec p hP
  have hflag := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW S (a.val + 1) a.2
    (fun i => ⟨fun h => ⟨a, ha, Nat.lt_succ_iff.1 h⟩, fun ⟨k, hk, hik⟩ =>
      Nat.lt_succ_iff.2 (le_trans hik (ha' k hk))⟩)
    (fun i => (S.filter fun k => k.val < i.val).card) (fun i => rfl)
  exact ⟨u, hflag.1 ▸ hu, l, hflag.2.1 ▸ hl, rfl⟩

theorem isCuspFun_slice : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι → (∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0) → ∀ s : GA D V' →* GA D V, (∀ h, EmbRel V V' ι (s h) h) → ∀ ψ ∈ cuspOn θ V X Y T U ε fr ρ c, ∀ y ∈ levi D.sp.cm.sig V.gram X Y T, (∀ t ∈ uPart D.sp.cm.sig V.gram X Y T, t * y = y * t) → IsCuspFun V' fun h => ψ (s h * y) := by
  intro D θ V U ε fr W _ _ ρ c m X Y hW T V' ι hι hr s hs ψ hψ y hy hyc
  obtain ⟨hcm, hJall⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hJ := hJall V
  have hJ' := hJall V'
  obtain ⟨s₀, hs₀c, hs₀, hs₀Q⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D V V' ι hι
  have es : ∀ h, s h = s₀ h := fun h => (hs₀ h (s h)).1 (hs h)
  have hsc : Continuous s := by
    have : (s : GA D V' → GA D V) = s₀ := funext es
    rw [this]; exact hs₀c
  have hsQ : ∀ γ ∈ GQ V', s γ ∈ GQ V := fun γ hγ => es γ ▸ hs₀Q γ hγ
  obtain ⟨hup, hsurj, -⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UEmb.range_embHom D V m X Y hW T V' ι hι hr s hs
  have hψl : ∀ γ ∈ leftSub V X Y T, ∀ g, ψ (γ * g) = ψ g := hψ.1.1.left
  have hψc : Continuous ψ := hψ.1.1.cont
  have hfl : ∀ γ ∈ GQ V', ∀ g, (fun h => ψ (s h * y)) (γ * g) = (fun h => ψ (s h * y)) g := fun γ hγ g => by
    have h1 : s γ ∈ leftSub V X Y T := Subgroup.mem_sup_right ⟨hsQ γ hγ,
      GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T (hup γ)⟩
    change ψ (s (γ * g) * y) = ψ (s g * y)
    rw [map_mul, mul_assoc, hψl _ h1]
  obtain ⟨m', e, X', Y', hsl, hW'⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.exists_sliceFrame D V m X Y hW T V' ι hι hr
  refine _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong D V' m' X' Y' hW' (_root_.GlobalTheory.CompanionTheory.IsoFrameBound.isoFrame_le_wittFrame D V' m' X' Y' hW') _ hfl fun k => ?_
  have hκ : e k ∉ upTo T := (hsl.2.1 _).2 ⟨k, rfl⟩
  have hκT : e k ∉ T := fun h => hκ ⟨_, h, le_rfl⟩
  have hTT' : T ⊂ insert (e k) T := Finset.ssubset_insert hκT
  have hψ0 := hψ.2 _ hTT'
  haveI := locallyCompact_unip hcm hJ' hW' {k}
  haveI := locallyCompact_unip hcm hJ hW (insert (e k) T)
  have hle := GlobalTheory.StdPar.unip_mono_of_subset _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW (insert (e k) T) T hTT'.1
  have hs1 := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.unip_embed D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k
  have hdown := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Down.mem_unip_of_image D V m X Y hW T V' ι hι hr m' e X' Y' hsl hW' s hs k
  have hdec : ∀ v ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∃ u ∈ unip D.sp.cm.sig V'.gram X' {k},
      v * (s u)⁻¹ ∈ unip D.sp.cm.sig V.gram X T := fun v hv => by
    obtain ⟨u, hu, l, hl, rfl⟩ := unip_split D V m X Y hW T _ hTT'.1 v hv
    have hl' : l ∈ unip D.sp.cm.sig V.gram X (insert (e k) T) := by
      simpa using mul_mem (inv_mem (hle hu)) hv
    obtain ⟨b, rfl⟩ := hsurj l (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.LeviU.levi_inf_unip_le_uPart D V m X Y hW T _ hκ ⟨hl, hl'⟩)
    exact ⟨b, hdown b hl', by simpa using hu⟩
  have hnorm : ∀ p ∈ unip D.sp.cm.sig V.gram X (insert (e k) T), ∀ a ∈ unip D.sp.cm.sig V.gram X T,
      p * a * p⁻¹ ∈ unip D.sp.cm.sig V.gram X T := fun p hp a ha =>
    conj_mem_unip_of_subset hcm hJ hW hTT'.1 hp ha
  obtain ⟨π, hπc, hπ, hπQ⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice.Proj.exists_proj D V m X Y hW T V' ι hι hr s hs _ _ hnorm hdec
  let s₁ : unip D.sp.cm.sig V'.gram X' {k} →* unip D.sp.cm.sig V.gram X (insert (e k) T) :=
    (s.comp (unip D.sp.cm.sig V'.gram X' {k}).subtype).codRestrict _ fun u => hs1 _ u.2
  have hs₁c : Continuous s₁ := (hsc.comp continuous_subtype_val).subtype_mk _
  have hπs : ∀ u, π (s₁ u) = u := fun u => (hπ _ _).2 (by
    change s u * (s u)⁻¹ ∈ _
    simp [one_mem])
  have hker : ∀ v, π v = 1 ↔ (v : GA D V) ∈ unip D.sp.cm.sig V.gram X T := fun v => by
    rw [hπ v 1]
    simp
  intro μ 𝓕 hμ h𝓕 h1 g
  have cN : GlobalTheory.Cusp.Cocompact (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T)) := cocompact_unip_std hcm hJ hW _
  have key := GlobalTheory.Cusp.constTermOn_eq_integral_semidirect (GA D V) (GA D V') (GQ V) _ _ (GQ V') _ hle cN
    (cocompact_unip_std hcm hJ hW T) (cocompact_unip_std hcm hJ' hW' {k}) s₁ π hs₁c hπc hπs hker
    (fun u hu => hsQ _ hu) (fun v hv => hπQ v hv) ψ hψc
    (fun a ha y => hψl a (Subgroup.mem_sup_left ha) y)
    (fun γ hγ hγ' y => hψl γ (ratPts_unip_le_leftSub D V m X Y hW T _ hTT'.1 ⟨hγ, hγ'⟩) y) μ 𝓕 hμ h𝓕 h1 (s g * y)
  obtain ⟨μ₀, 𝓕₀, a1, a2, a3⟩ := exists_mass_one cN
  have hz := hψ0 μ₀ 𝓕₀ a1 a2 a3 (s g * y)
  have hct : GlobalTheory.Cusp.constTermOn (GQ V) (unip D.sp.cm.sig V.gram X (insert (e k) T)) ψ (s g * y) = 0 := by
    haveI := a1
    have e1 := GlobalTheory.Cusp.Stages.constTermOn_eq' (Γ := GQ V) (φ := ψ) (x := s g * y) a2 (fun γ hγ n => by
      simp only [Subgroup.coe_mul, mul_assoc]
      exact hψl _ (ratPts_unip_le_leftSub D V m X Y hW T _ hTT'.1 ⟨hγ, (γ : unip _ _ _ _).2⟩) _)
    rw [e1, ← hz]
    simp
  rw [hct] at key
  refine key.trans (MeasureTheory.integral_congr_ae (.of_forall fun u => ?_))
  change ψ (s u * (s g * y)) = ψ (s (u * g) * y)
  rw [map_mul, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Slice
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviDecompositionHermitianCentralizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

theorem eichler_frame : ∀ {n m : ℕ} (ε : Fin n → Bool) (G Q : Matrix (Fin n) (Fin n) ℂ) (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m)),
    IsUnit Q → Qᴴ * Formalism.REAL.Jm ε * Q = G → xᴴ * G * x = 0 → xᴴ * G * y = 1 →
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * G ∈ Formalism.QuantumDeterminants.UH G ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)),
        Formalism.REAL.Jm ε *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (Q * (1 + x * u + w * xᴴ * G)) *ᵥ fun j => y j i)) := by
  intro n m ε G Q x y A hQ hG hxx hxy
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have h2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have ex : ∀ z : Matrix (Fin n) (Fin m) ℂ, xᴴ * G * z = (Q * x)ᴴ * Formalism.REAL.Jm ε * (Q * z) := fun z => by
    rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  obtain ⟨u, w, hu, hw, hux, hN, hJ⟩ := _root_.GlobalTheory.CompanionTheory.EichlerTransf.eichler_transformation ε (Q * x) (Q * y) A (by rw [← ex, hxx]) (by rw [← ex, hxy])
  refine ⟨u * Q, Q⁻¹ * w, fun i v hi => ?_, fun v i hi => ?_, fun i j hj => ?_, ?_⟩
  · simp [Matrix.mul_apply, hu i _ hi]
  · simp [Matrix.mul_apply, hw _ i hi]
  · rw [Matrix.mul_assoc]; exact hux i j hj
  have key : Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) = (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q := by
    rw [← hG, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Q⁻¹, h1, Matrix.one_mul]
  refine ⟨?_, ?_⟩
  · show _ = _
    have e : (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)ᴴ * G * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G) =
        (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G))ᴴ * Formalism.REAL.Jm ε * (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) := by
      rw [← hG, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e, key, Matrix.conjTranspose_mul]
    have hN' : _ = _ := hN
    calc Qᴴ * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) * Q)
        = Qᴴ * ((1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε)) * Q := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hN', ← hG, Matrix.mul_assoc]
  · have cx : ∀ z : Matrix (Fin n) (Fin m) ℂ, ∀ i : A, (Q * (1 + x * (u * Q) + Q⁻¹ * w * xᴴ * G)) *ᵥ (fun j => z j i) =
        (1 + Q * x * u + w * (Q * x)ᴴ * Formalism.REAL.Jm ε) *ᵥ fun j => (Q * z) j i := fun z i => by
      rw [key, ← Matrix.mulVec_mulVec]
      congr 1
    simp only [cx]
    exact hJ

theorem iwasawa_adapted : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (b : GA D V), ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ mm ∈ levi D.sp.cm.sig V.gram X Y T, ∃ b₀ : GA D V, b = n * mm * b₀ ∧ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.IsAdapted V X Y T ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) := by
  intro D θ hθ V ε fr hfr m X Y hW T b
  classical
  have hQ := isFrameFam_mul_infMat_inv D θ hθ V ε fr hfr b
  let Q : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹
  let x : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => X.map (tauE D τ)
  let y : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ := fun τ => Y.map (tauE D τ)
  have hmap : ∀ τ (Z Z' : Matrix (Fin V.rank) (Fin m) D.host.E), (Z.map (tauE D τ))ᴴ * gramAt D V τ * Z'.map (tauE D τ) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z * V.gram * Z').map (tauE D τ) := by
    intro τ Z Z'
    have e : (Z.map (tauE D τ))ᴴ = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Z).map (tauE D τ) := by
      ext i j
      simp [Formalism.UG.cT, GlobalTheory.Mem.Isom.tauE_sig]
    rw [e, gramAt, Matrix.map_mul, Matrix.map_mul]
  have hxx : ∀ τ, (x τ)ᴴ * gramAt D V τ * x τ = 0 := fun τ => by
    rw [hmap, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have hxy : ∀ τ, (x τ)ᴴ * gramAt D V τ * y τ = 1 := fun τ => by
    rw [hmap, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  choose u w hu hw hux hN hJ using fun τ =>
    eichler_frame (ε τ) (gramAt D V τ) (Q τ) (x τ) (y τ) (upTo T) (hQ τ).1 (hQ τ).2 (hxx τ) (hxy τ)
  obtain ⟨g, hg, U, W, hU, hW', hUX, hgM⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.exists_adelic_of_real_comps D θ hθ V X u w hN
  have hgu : g ∈ unip D.sp.cm.sig V.gram X T :=
    GlobalTheory.T.unitary_adelic_unipotent_lift D.sp.cm.sig V.gram X T g U W hW.xx (fun i v hi => hU i v fun τ => hu τ i v hi)
      (fun v i hi => hW' v i fun τ => hw τ v i hi) (fun i j hj => hUX i j fun τ => hux τ i j hj) hgM
  refine ⟨g, hgu, 1, one_mem _, g⁻¹ * b, by rw [mul_one, mul_inv_cancel_left], fun τ => ?_⟩
  have e1 : (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) g := by
    rw [Formalism.L2.Fam.ThC.infMat_mul, Matrix.mul_inv_rev]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Formalism.L2.Fam.ThC.infMat_mul, mul_inv_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have e2 : fr τ * (infMat D.sp.cm.sig V.gram (θ τ) (g⁻¹ * b))⁻¹ =
      fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ * (1 + x τ * u τ + w τ * (x τ)ᴴ * gramAt D V τ) := by
    rw [e1, hg τ, ← Matrix.mul_assoc]
  obtain ⟨k, S, hk⟩ := GlobalTheory.T.involution_stable_subspace_coordinate (ε τ) _ (hJ τ)
  refine ⟨k, S, ?_⟩
  beta_reduce
  rw [e2]
  exact hk

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

