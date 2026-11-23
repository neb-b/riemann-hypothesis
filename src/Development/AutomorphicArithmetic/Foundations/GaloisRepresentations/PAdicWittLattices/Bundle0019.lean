module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTatePull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

theorem pTatePull : TatePull := by
  unfold TatePull
  intro p _ D R _ _ gb S S' s s' f N o o' m k _ t
  have hT := HeckeRestrict.tate_pullback D.toG o.A o'.A o.act o'.act o.P o'.P o.isLB o'.isLB f m.φ m.φ₂
    m.cart m.sq m.act m.pol k t
  have hpt : ∀ y, (toUnit (Over.mk (t ≫ f)) ≫ o.eta y).left = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left, m.eta y]
    exact Category.assoc _ _ _
  have hpt' : ∀ y, (toUnit (Over.mk t) ≫ o'.eta y).left ≫ m.φ = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left]
    exact Category.assoc _ _ _
  refine ⟨fun I => ?_, fun I' => ?_⟩
  · obtain ⟨I', hI'⟩ := hT.2 I
    refine ⟨I', fun hI y => ?_, fun n x => (hI' n x).symm⟩
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hpt', ← hpt, hI y, hI' N y]
    · rw [Over.w, Over.w]
  · obtain ⟨I, hI⟩ := hT.1 I'
    refine ⟨I, fun hI' y => ?_, fun n x => (hI n x).symm⟩
    apply Over.OverMorphism.ext
    rw [hpt, hI N y, ← hI' y, hpt']

end UpperTheory.Gal.G3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem square_map_comp {S : Scheme.{0}} {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (f : A ⟶ B) (g : B ⟶ C) :
    Hecke.sq2 f ≫ Hecke.sq2 g = Hecke.sq2 (f ≫ g) := by
  unfold Hecke.sq2
  rw [← Over.comp_left]
  congr 1
  ext <;> simp

private theorem square_map_id {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] :
    Hecke.sq2 (𝟙 A) = 𝟙 _ := by
  simp [Hecke.sq2]

private theorem cls_pow' {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) (n : ℕ) (h : (Hecke.lbPow P n).IsLB) :
    GlobalTheory.CechPic.cls (Hecke.lbPow P n) h = n • GlobalTheory.CechPic.cls P hP := by
  unfold Hecke.lbPow at h ⊢
  rw [GlobalTheory.CechPic.cls_linComb hP]
  simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

private theorem bundle_cancel {S : Scheme.{0}} {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (θ : A ⟶ B) [IsIso θ] (χ : B ⟶ C) (P : LB (G2 A).left) (Q : LB (G2 B).left)
    (T : LB (G2 C).left) (hP : P.IsLB) (hQ : Q.IsLB) (hT : T.IsLB) (c : ℕ)
    (h₁ : LBIso (Hecke.lbPow P 1) (Q.pull (Hecke.sq2 θ)))
    (h₂ : LBIso (Hecke.lbPow P c) (T.pull (Hecke.sq2 (θ ≫ χ)))) :
    LBIso (Hecke.lbPow Q c) (T.pull (Hecke.sq2 χ)) := by
  have hQθ := pull_isLB hQ (Hecke.sq2 θ)
  have hTχ := pull_isLB hT (Hecke.sq2 χ)
  have hTθχ := pull_isLB hT (Hecke.sq2 (θ ≫ χ))
  have hP1 : (Hecke.lbPow P 1).IsLB := LB.isLB_linComb hP _ _
  have hPc : (Hecke.lbPow P c).IsLB := LB.isLB_linComb hP _ _
  have hQc : (Hecke.lbPow Q c).IsLB := LB.isLB_linComb hQ _ _
  rw [← GlobalTheory.CechPic.cls_eq_iff hP1 hQθ, cls_pow' hP, GlobalTheory.CechPic.cls_pull hQ] at h₁
  rw [← GlobalTheory.CechPic.cls_eq_iff hPc hTθχ, cls_pow' hP, GlobalTheory.CechPic.cls_pull hT] at h₂
  rw [← GlobalTheory.CechPic.cls_eq_iff hQc hTχ, cls_pow' hQ, GlobalTheory.CechPic.cls_pull hT]
  have key : ∀ x, GlobalTheory.CechPic.pull (Hecke.sq2 (inv θ)) (GlobalTheory.CechPic.pull (Hecke.sq2 θ) x) = x := by
    intro x
    rw [← GlobalTheory.CechPic.pull_comp, square_map_comp, IsIso.inv_hom_id, square_map_id, GlobalTheory.CechPic.pull_id]
  rw [← key (c • _), ← key (GlobalTheory.CechPic.pull (Hecke.sq2 χ) _), map_nsmul, ← h₁, one_smul, h₂,
    ← square_map_comp, GlobalTheory.CechPic.pull_comp]

theorem UpperTheory.Gal.G3.pTransCancel :
    MultBasic → RelComp → TateDiff → TateTwist → TransIso → TransCancel := by
  intro hMB hRC hTD hTT hTI p _ D G L R _ _ gb S s M N' N o o₁ o₂ θ χ h hint hadm hθ hθχ
  have hθiso : IsIso θ := hTI p D G L R gb S s M N' o o₁ θ 1 (one_mem _) hθ
  obtain ⟨hθm, hθa, ⟨θ', d₁, hθ'm, hθ'a, hθθ', hθ'θ, hd₁⟩, ⟨c₁, hc₁, ⟨hPθ⟩, t₁, t₁', ht₁, ht₁', htt₁, hc₁e⟩, hθpt⟩ := hθ
  obtain ⟨hχm₀, hχa₀, ⟨ω, d, hωm, hωa, hχω, hωχ, hd⟩, ⟨c, hc, ⟨hPχ⟩, t, t', ht, ht', htt, hce⟩, hχpt⟩ := hθχ
  have hinvm : IsMonHom (inv θ) := by
    constructor
    · rw [← cancel_mono θ]
      simp
    · rw [← cancel_mono θ]
      simp [IsMonHom.mul_hom]
  have hχm : IsMonHom χ := by
    have e : χ = inv θ ≫ (θ ≫ χ) := by simp
    rw [e]
    infer_instance
  have hc1 : c₁ = 1 :=
    (hMB p).1 _ c₁ 1 hc₁ (Nat.coprime_one_left p) ⟨t₁, t₁', ht₁, ht₁', htt₁, hc₁e⟩
      ((hMB p).2.2 D G L 1 (one_mem _))
  subst hc1
  refine ⟨hχm, ?_, ⟨ω ≫ θ, d, inferInstance, ?_, ?_, ?_, hd⟩,
    ⟨c, hc, ⟨bundle_cancel θ χ o.P o₁.P o₂.P o.isLB o₁.isLB o₂.isLB c hPθ hPχ⟩, t, t', ht, ht', htt, hce⟩, ?_⟩
  · intro e
    rw [← cancel_epi θ, ← Category.assoc, ← hθa e, Category.assoc, hχa₀ e, Category.assoc]
  · intro e
    rw [← Category.assoc, hωa e, Category.assoc, hθa e, Category.assoc]
  · rw [← cancel_epi θ]
    simp only [← Category.assoc]
    rw [hχω, MonObj.pow_comp, MonObj.comp_pow]
    simp
  · rw [Category.assoc]
    exact hωχ
  · intro k _ _ tt β htβ
    obtain ⟨I, I₁, hI, hI₁, hr₁⟩ := hθpt k tt β htβ
    obtain ⟨J, J₂, hJ, hJ₂, hr₂⟩ := hχpt k tt β htβ
    obtain ⟨u, hu, hIJ⟩ := hTD p D G L R gb S s M o k tt I J hI hJ
    obtain ⟨J', hJ', hJJ'⟩ := hTT p D G L R gb S s N o₂ k tt J₂ hJ₂ (h * u⁻¹ * h⁻¹) (hadm _ (inv_mem hu))
    have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
    have hu'1 : h * u⁻¹ * h⁻¹ ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) (hadm _ (inv_mem hu))
    have r0 : UpperTheory.Gal.G3.Rel L I₁ I (inv θ) 1 := by
      intro n hn hnp x y
      have e : I₁.ev n x ≫ inv θ = I.ev n y ↔ I.ev n y ≫ θ = I₁.ev n x := by
        constructor
        · intro e
          rw [← e]
          simp
        · intro e
          rw [← e]
          simp
      rw [e, hr₁ n hn hnp y x]
      simp only [map_one, Module.End.one_apply]
      constructor
      · rintro ⟨v, hv, e⟩
        exact ⟨-v, neg_mem hv, by rw [e]; simp⟩
      · rintro ⟨v, hv, e⟩
        exact ⟨-v, neg_mem hv, by rw [e]; simp⟩
    have r1 := (hRC p D G L R gb S s N' M M o₁ o o k tt I₁ I J (inv θ) (𝟙 o.A) 1 u inferInstance
      inferInstance (UpperTheory.Gal.Int.Geo.integ_of_mem hu1)).2 r0 hIJ
    have r2 := (hRC p D G L R gb S s N' M N o₁ o o₂ k tt I₁ J J₂ (inv θ ≫ 𝟙 o.A) (θ ≫ χ) (u * 1) h
      inferInstance inferInstance hint).2 r1 hr₂
    have r3 := (hRC p D G L R gb S s N' N N o₁ o₂ o₂ k tt I₁ J₂ J' ((inv θ ≫ 𝟙 o.A) ≫ (θ ≫ χ))
      (𝟙 o₂.A) (h * (u * 1)) (h * u⁻¹ * h⁻¹) inferInstance inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem hu'1)).2 r2 hJJ'
    have e1 : ((inv θ ≫ 𝟙 o.A) ≫ (θ ≫ χ)) ≫ 𝟙 o₂.A = χ := by simp
    have e2 : h * u⁻¹ * h⁻¹ * (h * (u * 1)) = h := by group
    rw [e1, e2] at r3
    exact ⟨I₁, J', hI₁, hJ', r3⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransIso :
    IsoPts → IsogFEt → TransIso := by
  intro IP IF p _ D G L R _ _ gb S s N' N o' o ψ u hu T
  obtain ⟨hmon, -, ⟨ψ', d, hψ', -, hd, hd', hdp⟩, -, tate⟩ := T
  haveI := hmon
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  obtain ⟨hfin, het, hsurj⟩ := IF R S s o'.A o.A o'.ab o.ab ψ ψ' d hd0 hmon hψ' hd hd'
  haveI := het
  haveI := hfin
  have hiso : IsIso ψ.left := by
    apply IP ψ.left
    intro Ω _ _ z
    obtain ⟨v, hv⟩ := hsurj.surj (UpperTheory.Gal.TranscendenceTraces.pt z)
    obtain ⟨y, hy, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ.left Ω z v hv
    refine ⟨y, hy, fun y₂ hy₂ => ?_⟩
    let t : sp Ω ⟶ S := y ≫ o'.A.hom
    have ht2 : y₂ ≫ o'.A.hom = t := by
      rw [← Over.w ψ, ← Category.assoc, hy₂, ← hy, Category.assoc, Over.w ψ]
    let a₁ : Over.mk t ⟶ o'.A := Over.homMk y rfl
    let a₂ : Over.mk t ⟶ o'.A := Over.homMk y₂ ht2
    have hc : a₁ ≫ ψ = a₂ ≫ ψ := by
      ext
      simp [a₁, a₂, hy, hy₂]
    have ha : (a₂ * a₁⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, ← hc, mul_inv_cancel]
    have had : (a₂ * a₁⁻¹) ^ d = 1 := by
      have e : (a₂ * a₁⁻¹) ^ d = (a₂ * a₁⁻¹) ≫ ψ ≫ ψ' := by
        rw [hd, MonObj.comp_pow, Category.comp_id]
      rw [e, ← Category.assoc, ha, MonObj.one_comp]
    let β : R →+* Ω := (Spec.preimage (t ≫ s)).hom
    have hβ : t ≫ s = spMap β := by
      simp [β, spMap, Spec.map_preimage]
    obtain ⟨I', I'', -, -, hrel⟩ := tate Ω t β hβ
    obtain ⟨x, hx⟩ := (I'.onto d hd0 _).mp had
    have h0 : I'.ev d x ≫ ψ = I''.ev d 0 := by
      rw [hx, ha, HeckeRestrict.ev_zero]
    obtain ⟨w, hw, hxw⟩ := (hrel d hd0 hdp x 0).mp h0
    have hinv : u⁻¹ ∈ L.KN 1 := Subgroup.inv_mem _ hu
    have hdw : d • w = L.actG u (inAf D x) := by
      rw [hxw]
      simp [inAf]
    have hxa : inAf D x = d • L.actG u⁻¹ w := by
      rw [← map_nsmul, hdw, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    obtain ⟨z', hz'⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x d hd0 hdp _
      (UpperTheory.Gal.Int.Geo.integ_of_mem hinv w hw) hxa
    have h1 : a₂ * a₁⁻¹ = 1 := by
      rw [← hx]
      exact (I'.ker d hd0 x).mpr ⟨z', hz'⟩
    have h2 : a₂ = a₁ := mul_inv_eq_one.mp h1
    exact congrArg Over.Hom.left h2
  have : IsIso ((Over.forget S).map ψ) := hiso
  exact isIso_of_reflects_iso ψ (Over.forget S)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {R : Type} [CommRing R] [Algebra ℚ R]
  {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem comp_pow_overScheme_grpObj {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    f ≫ x ^ n = (f ≫ x) ^ n := MonObj.comp_pow x n f

private theorem pow_comp_monHom_overScheme_grpObj {A B T : Over S} [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (x : T ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n := MonObj.pow_comp x n φ

private theorem pt_transfer {N' N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {o : GObj gb N' s} {o₁ o₂ : GObj gb N s}
    {ψ₁ : o.A ⟶ o₁.A} {ψ₂ : o.A ⟶ o₂.A} {ψ' : o₁.A ⟶ o.A} {d : ℕ} (hψ' : IsMonHom ψ')
    (hd : ψ₁ ≫ ψ' = (𝟙 o.A) ^ d) (hdp : d.Coprime p) {h : G.GAf} {k : Type} [Field k] {t : Sp k ⟶ S}
    (I : UpperTheory.Gal.Int.Geo.TIso o t) (J₁ : UpperTheory.Gal.Int.Geo.TIso o₁ t) (J₂ : UpperTheory.Gal.Int.Geo.TIso o₂ t)
    (H₁ : Rel L I J₁ ψ₁ h) (H₂ : Rel L I J₂ ψ₂ h) (a : Over.mk t ⟶ o.A) (y : D.La)
    (ha : a ≫ ψ₁ = J₁.ev N y) : a ≫ ψ₂ = J₂.ev N y := by
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  have hn : 0 < N * d := Nat.mul_pos hN hd0
  have hnp : (N * d).Coprime p := Nat.Coprime.mul_left hNp hdp
  have h1 : (a ≫ ψ₁) ^ N = 1 := by
    rw [ha]
    exact (J₁.onto N hN _).mpr ⟨y, rfl⟩
  have h2 : a ^ d = (a ≫ ψ₁) ≫ ψ' := by
    rw [Category.assoc, hd, comp_pow_overScheme_grpObj, Category.comp_id]
  have h3 : a ^ (N * d) = 1 := by
    rw [mul_comm, pow_mul, h2, ← pow_comp_monHom_overScheme_grpObj, h1, MonObj.one_comp]
  obtain ⟨x, hx⟩ := (I.onto (N * d) hn a).mp h3
  let y' : D.toG.La := y
  have hJ₁ : J₁.ev N y' = J₁.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₁.tower N d hN hd0]
  have hJ₂ : J₂.ev N y' = J₂.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₂.tower N d hN hd0]
  change a ≫ ψ₁ = J₁.ev N y' at ha
  change a ≫ ψ₂ = J₂.ev N y'
  rw [← hx] at ha ⊢
  rw [hJ₂]
  rw [hJ₁] at ha
  exact (H₂ (N * d) hn hnp x (d • y')).mpr ((H₁ (N * d) hn hnp x (d • y')).mp ha)

end

theorem UpperTheory.Gal.G3.pTransKer :
    RelComp → TateDiff → TateTwist → TransKer := by
  intro RC TD TT p _ D G L R _ _ gb S s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm T₁ T₂ k _ _ t
  let β : R →+* k := (Spec.preimage (t ≫ s)).hom
  have hβ : t ≫ s = spMap β := by
    simp [β, spMap, Spec.map_preimage]
  have key : ∀ (q₁ q₂ : GObj gb (↑N) s) (φ₁ : o.A ⟶ q₁.A) (φ₂ : o.A ⟶ q₂.A),
      IsTrans L h o q₁ φ₁ → IsTrans L h o q₂ φ₂ → ∀ (a : Over.mk t ⟶ o.A) (y : D.La),
      a ≫ φ₁ = toUnit (Over.mk t) ≫ q₁.eta y → a ≫ φ₂ = toUnit (Over.mk t) ≫ q₂.eta y := by
    intro q₁ q₂ φ₁ φ₂ U₁ U₂ a y ha
    obtain ⟨-, -, ⟨φ', d, hφ', -, hd, -, hdp⟩, -, tate₁⟩ := U₁
    obtain ⟨hmon₂, -, -, -, tate₂⟩ := U₂
    obtain ⟨I₁, J₁, hI₁, hJ₁, R₁⟩ := tate₁ k t β hβ
    obtain ⟨I₂, J₂, hI₂, hJ₂, R₂⟩ := tate₂ k t β hβ
    obtain ⟨u, hu, hR⟩ := TD p D G L R gb S s N' o k t I₁ I₂ hI₁ hI₂
    have hc₁ := (RC p D G L R gb S s (↑N') (↑N') (↑N) o o q₂ k t I₁ I₂ J₂ (𝟙 _) φ₂ u h
      inferInstance hmon₂ hint).2 hR R₂
    have hw : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hadm _ (Subgroup.inv_mem _ hu)
    obtain ⟨J₃, hJ₃, hR₃⟩ := TT p D G L R gb S s N q₂ k t J₂ hJ₂ _ hw
    have hwi : Integ L (h * u⁻¹ * h⁻¹) :=
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hw)
    have hc₂ := (RC p D G L R gb S s (↑N') (↑N) (↑N) o q₂ q₂ k t I₁ J₂ J₃ (𝟙 _ ≫ φ₂) (𝟙 _) (h * u) _
      inferInstance inferInstance hwi).2 hc₁ hR₃
    have hg : h * u⁻¹ * h⁻¹ * (h * u) = h := by group
    rw [hg, Category.id_comp, Category.comp_id] at hc₂
    have hN : 0 < (N : ℕ) := lt_of_lt_of_le (by norm_num) N.2.1
    rw [hJ₁ y] at ha
    rw [hJ₃ y]
    exact pt_transfer hN N.2.2 hφ' hd hdp I₁ J₁ J₃ R₁ hc₂ a y ha
  have hz : ∀ q : GObj gb (↑N) s, toUnit (Over.mk t) ≫ q.eta (0 : D.La) = 1 := by
    intro q
    rw [show q.eta (0 : D.La) = 1 from q.eta_zero, MonObj.comp_one]
  refine ⟨fun a => ⟨fun h1 => ?_, fun h2 => ?_⟩, fun a y => ⟨key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a y, key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a y⟩⟩
  · have := key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a 0 (by rw [h1, hz])
    rwa [hz] at this
  · have := key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a 0 (by rw [h2, hz])
    rwa [hz] at this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransUniqPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransUniqPt :
    MultBasic → IsogFEt → TransKer → QuotUniq → PolUniq → MapOfIso → TransUniqPt := by
  intro hMB hFE hTK hQU hPU hMI p _ D G L R _ _ gb k _ _ s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  have hK := hTK p D G L R gb (Sp k) s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  obtain ⟨mon₁, -, ⟨ψ₁', d₁, mon₁', -, e₁, e₁', cop₁⟩, ⟨c₁, hc₁, ⟨lb₁⟩, t₁, t₁', i₁, i₁', tt₁, hm₁⟩, -⟩ := id tr₁
  obtain ⟨mon₂, -, ⟨ψ₂', d₂, mon₂', -, e₂, e₂', cop₂⟩, ⟨c₂, hc₂, ⟨lb₂⟩, t₂, t₂', i₂, i₂', tt₂, hm₂⟩, -⟩ := id tr₂
  have dpos : ∀ d : ℕ, d.Coprime p → 0 < d := fun d hd => Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hd)
  obtain ⟨f₁, et₁, sj₁⟩ := hFE R (Sp k) s o.A o₁.A o.ab o₁.ab ψ₁ ψ₁' d₁ (dpos _ cop₁) mon₁ mon₁' e₁ e₁'
  obtain ⟨f₂, et₂, sj₂⟩ := hFE R (Sp k) s o.A o₂.A o.ab o₂.ab ψ₂ ψ₂' d₂ (dpos _ cop₂) mon₂ mon₂' e₂ e₂'
  obtain ⟨θ, isoθ, monθ, hθ⟩ := hQU k o.A o₁.A o₂.A o.ab o₁.ab o₂.ab ψ₁ ψ₂ mon₁ mon₂ f₁ et₁ sj₁ f₂ et₂ sj₂
    (fun Ω _ _ t a => (hK Ω t).1 a)
  have lin₁ := tr₁.2.1
  have lin₂ := tr₂.2.1
  haveI := f₁
  haveI := et₁
  haveI := sj₁
  haveI : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have cancel : ∀ {X : Over (Sp k)} (a b : o₁.A ⟶ X), ψ₁ ≫ a = ψ₁ ≫ b → a = b := fun a b e =>
    Over.OverMorphism.ext ((cancel_epi ψ₁.left).1 (by simpa using congrArg (·.left) e))
  have lin : ∀ c, o₁.act.act c ≫ θ = θ ≫ o₂.act.act c := fun c => cancel _ _ (by
    rw [← Category.assoc, ← lin₁ c, Category.assoc, hθ, lin₂ c, ← hθ, Category.assoc])
  have hcc : c₁ = c₂ := (hMB p).1 (mul h) c₁ c₂ hc₁ hc₂ ⟨t₁, t₁', i₁, i₁', tt₁, hm₁⟩ ⟨t₂, t₂', i₂, i₂', tt₂, hm₂⟩
  subst hcc
  have hPo := o.isLB
  have hP1 := o₁.isLB
  have hP2 := o₂.isLB
  have hQ : (o₂.P.pull (Hecke.sq2 θ)).IsLB := pull_isLB hP2 _
  have sqc : Hecke.sq2 ψ₁ ≫ Hecke.sq2 θ = Hecke.sq2 ψ₂ := by
    rw [← hθ]
    simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc]
  have key : LBIso (o₁.P.pull (Hecke.sq2 ψ₁)) ((o₂.P.pull (Hecke.sq2 θ)).pull (Hecke.sq2 ψ₁)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP1 _) (pull_isLB hQ _)).1 ?_
    have a1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP1 _)).2 lb₁
    have a2 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP2 _)).2 lb₂
    rw [← a1, a2, GlobalTheory.CechPic.cls_pull hP2, GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2,
      ← GlobalTheory.CechPic.pull_comp, sqc]
  have r₁ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₁, map_zero]
  have r₂ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₂, map_zero]
  have pol : LBIso o₁.P (o₂.P.pull (Hecke.sq2 θ)) :=
    hPU (Sp k) o.A o₁.A o.ab o₁.ab ψ₁ mon₁ f₁ et₁ sj₁ o₁.P _ hP1 hQ o₁.rig₁ o₁.rig₂ r₁ r₂ key
  have lev : ∀ y, o₁.eta y ≫ θ = o₂.eta y := by
    intro y
    obtain ⟨v, hv⟩ := sj₁.surj (UpperTheory.Gal.TranscendenceTraces.pt (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ₁.left k (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left v hv
    let a : Over.mk (𝟙 (Sp k)) ⟶ o.A := Over.homMk z (by
      have w1 := Over.w ψ₁
      have w2 := Over.w (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y)
      simp only [Over.mk_hom] at w2 ⊢
      rw [← w1, ← Category.assoc, hz, w2])
    have ha : a ≫ ψ₁ = toUnit _ ≫ o₁.eta y := Over.OverMorphism.ext hz
    have hb := ((hK k (𝟙 _)).2 a y).1 ha
    have e : toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y ≫ θ = toUnit (Over.mk (𝟙 (Sp k))) ≫ o₂.eta y := by
      rw [← Category.assoc, ← ha, Category.assoc, hθ, hb]
    let i : 𝟙_ (Over (Sp k)) ⟶ Over.mk (𝟙 (Sp k)) := Over.mkIdTerminal.from _
    have hi : i ≫ toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 _ := toUnit_unique _ _
    have e' := congrArg (i ≫ ·) e
    simpa [← Category.assoc, hi] using e'
  obtain ⟨m, hm⟩ := hMI D.toG R gb (Sp k) s N.1 o₁ o₂ θ isoθ monθ lin pol lev
  exact ⟨m, by rw [hm, ← hθ, Over.comp_left]⟩
end

