module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.EtCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.PWitScal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ)

private theorem ev_nsmul {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n : ℕ) (hn : 0 < n) (d : ℕ) (x : G.La) :
    I.ev n (d • x) = I.ev n x ^ d := by
  have h0 : I.ev n 0 = 1 := by
    have := I.add n 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  induction d with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ d ih => rw [succ_nsmul, I.add, ih, pow_succ]

private theorem isMonHom_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  constructor
  · rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]
  · rw [MonObj.comp_pow, Category.comp_id, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst,
      tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, mul_pow]

private theorem pow_comp_hom {S : Scheme.{0}} {A B Z : Over S} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f]
    (x : Z ⟶ A) (n : ℕ) : (x ^ n) ≫ f = (x ≫ f) ^ n := MonObj.pow_comp x n f

theorem UpperTheory.Gal.FixZ.witScal_of :
    UpperTheory.Gal.G3.RelComp → UpperTheory.Gal.FixZ.WitScal := by
  intro hR p _ D G L gb N X d z hd hdp hz
  obtain ⟨-, hact, hmul⟩ := hz
  have hid : ∃ m : GObjMap X.univ X.univ (𝟙 X.X), m.φ = 𝟙 _ :=
    ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id X.univ.A, sq := ⟨by simp, by simp⟩,
       act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id X.univ.isLB, eta := fun y => by simp }, rfl⟩
  obtain ⟨m, hm⟩ := hid
  have hmon : IsMonHom ((𝟙 X.univ.A) ^ d) := isMonHom_pow _ d
  have hcomm : ∀ c : D.O, X.univ.act.act c ≫ ((𝟙 X.univ.A) ^ d) = ((𝟙 X.univ.A) ^ d) ≫ X.univ.act.act c := by
    intro c
    haveI := X.univ.act.hom c
    rw [MonObj.comp_pow, pow_comp_hom, Category.comp_id, Category.id_comp]
  refine ⟨Category.id_comp _, X.univ, (𝟙 X.univ.A) ^ d, m, ?_, by rw [hm]; simp⟩
  refine ⟨hmon, hcomm, ⟨𝟙 _, d, inferInstance, fun c => ?_, Category.comp_id _, Category.id_comp _, hdp⟩,
    ⟨d ^ 2, hdp.pow_left 2, ⟨GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple _ _ X.univ.ab X.univ.P X.univ.isLB X.univ.rig₁ X.univ.rig₂ X.univ.ample d⟩, hmul⟩,
    fun k _ _ t β ht => ?_⟩
  · rw [Category.comp_id, Category.id_comp]
  · obtain ⟨I, hI⟩ := X.univ.geom k t β ht
    refine ⟨I, I, hI, hI, fun n hn hnp x y => ?_⟩
    have h1 := (hR p D G L ℂ gb X.X X.s _ _ _ X.univ X.univ X.univ k t I I I (𝟙 _) (𝟙 _) 1 1 inferInstance inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _))).1 n hn hnp (d • x) y
    have hev : I.ev n x ≫ ((𝟙 X.univ.A) ^ d) = I.ev n (d • x) ≫ 𝟙 _ := by
      rw [MonObj.comp_pow, Category.comp_id, Category.comp_id]
      exact (ev_nsmul I n hn d x).symm
    have hin : inAf D (d • x) = d • inAf D x := GlobalTheory.AdelicSim.inAf_nsmul D d x
    rw [hev, h1]
    simp only [map_one, Module.End.one_apply, hin, hact]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.TrEqRe
section
open NumberField Polynomial GlobalTheory.UPel.HT GlobalTheory.LKGeo GlobalTheory.LKTrip

namespace UpperTheory.Gal.FixZ

variable {p : ℕ} [Fact p.Prime]

private lemma conj_ne (D : Datum p) : (starRingEnd ℂ) D.ρc ≠ D.ρc := by
  intro h
  have him : D.ρc.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre : D.ρc = (D.ρc.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hroot := D.ρc_root
  rw [hre] at hroot
  have hr : D.ρc.re ^ 2 - (D.tr : ℝ) * D.ρc.re + (D.nm : ℝ) = 0 := by
    exact_mod_cast hroot
  have hd : ((D.tr : ℝ)) ^ 2 - 4 * (D.nm : ℝ) < 0 := by exact_mod_cast D.disc_neg
  nlinarith [sq_nonneg (2 * D.ρc.re - (D.tr : ℝ))]

private lemma tr_eq_re (D : Datum p) : (D.tr : ℂ) = D.ρc + (starRingEnd ℂ) D.ρc := by
  have hne : D.ρc - (starRingEnd ℂ) D.ρc ≠ 0 := sub_ne_zero.mpr (Ne.symm (conj_ne D))
  have h1 := D.ρc_root
  have h2 : ((starRingEnd ℂ) D.ρc) ^ 2 - (D.tr : ℂ) * (starRingEnd ℂ) D.ρc + (D.nm : ℂ) = 0 := by
    have := congrArg (starRingEnd ℂ) h1
    simpa using this
  apply mul_left_cancel₀ hne
  linear_combination h2 - h1

private lemma eps_eq (D : Datum p) : W2.epsD D = LocalSmoothExtension.epsOf D := by
  funext τ
  have hω : ((D.ω : D.F)) ^ 2 - (D.tr : D.F) * (D.ω : D.F) + (D.nm : D.F) = 0 := by
    have h1 : (D.ω : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have h2 := congrArg (algebraMap (𝓞 D.F) D.F) h1
    simpa only [map_sub, map_add (f := _), map_mul, map_pow, map_intCast, map_zero] using h2
  have hτ : (τ (D.ω : D.F)) ^ 2 - (D.tr : ℂ) * τ (D.ω : D.F) + (D.nm : ℂ) = 0 := by
    have := congrArg τ hω
    simpa using this
  have hfac : (τ (D.ω : D.F) - D.ρc) * (τ (D.ω : D.F) - (starRingEnd ℂ) D.ρc) = 0 := by
    have h1 := D.ρc_root
    have h2 := tr_eq_re D
    rw [h2] at h1 hτ
    linear_combination hτ - h1
  unfold W2.epsD LocalSmoothExtension.epsOf
  by_cases h : τ (D.ω : D.F) = D.ρc
  · have : τ (D.ω : D.F) ≠ (starRingEnd ℂ) D.ρc := by
      rw [h]; exact Ne.symm (conj_ne D)
    simp [h, Ne.symm (conj_ne D)]
  · have h' : τ (D.ω : D.F) = (starRingEnd ℂ) D.ρc := by
      rcases mul_eq_zero.mp hfac with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) h
      · exact sub_eq_zero.mp h0
    rw [if_neg h, if_pos h']

private lemma map_inv {K K' : Type} [Field K] [Field K'] (f : K →+* K') (P : K[X]) :
    (W2.invPoly P).map f = LocalSmoothExtension.invPol (P.map f) := by
  unfold W2.invPoly LocalSmoothExtension.invPol
  rw [Polynomial.map_mul, Polynomial.map_C, map_inv₀, Polynomial.coeff_map]
  congr 1
  simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]

private lemma kap_iff {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1) (i₀ : Fin D.a)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) :
    (∀ x, v.embedding (L.e x) = D.tau i₀ x) ↔ v.embedding (L.e (D.ω : D.F)) = D.ρc := by
  refine ⟨fun h => (h _).trans (D.tau_ω i₀), fun h => ?_⟩
  obtain ⟨i, hi⟩ := (L.sig v).mp hv
  have hii : i = i₀ := by
    haveI : Subsingleton (Fin D.a) := by rw [ha]; infer_instance
    exact Subsingleton.elim _ _
  subst hii
  have hs : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = D.tau i x := fun x => L.s_C i x
  rcases InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i)) with e | e
  · intro x
    rw [hi, e]
    exact hs x
  · exfalso
    rw [hi, e, ComplexEmbedding.conjugate_coe_eq, hs, D.tau_ω] at h
    exact conj_ne D h

private lemma kap_eq {D : Datum p} {G : HTGroup p} (L : Link D G) (ha : D.a = 1) (i₀ : Fin D.a)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (μ : ℂ) :
    (W2.kap L v (D.tau i₀) μ)⁻¹ = LocalSmoothExtension.markOf L v μ := by
  unfold W2.kap LocalSmoothExtension.markOf
  by_cases h : v.embedding (L.e (D.ω : D.F)) = D.ρc
  · rw [if_pos ((kap_iff L ha i₀ v hv).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((kap_iff L ha i₀ v hv).mp h')), if_neg h]

end UpperTheory.Gal.FixZ

theorem UpperTheory.Gal.FixZ.wtEq_of :
    UpperTheory.Gal.FixZ.WtEq := by
  intro p _ D G L ha i₀ v hv k α y
  funext P μ
  unfold UpperTheory.Gal.W2.wtFix UpperTheory.Gal.LocalSmoothExtension.cW UpperTheory.Gal.LocalSmoothExtension.endPol
  rw [UpperTheory.Gal.FixZ.eps_eq, UpperTheory.Gal.FixZ.map_inv, UpperTheory.Gal.FixZ.kap_eq L ha i₀ v hv μ]
end

