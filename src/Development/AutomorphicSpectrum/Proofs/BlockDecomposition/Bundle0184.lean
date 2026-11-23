module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0168
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0177
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRestrictFirstPieceCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

section Cuts

variable {d : ℕ} (E : Frame (Φ := Φ) (d + 1)) (E' : Frame (Φ := Φ') (d + 1)) (e : E.D ⟶ m.G.obj E'.D)
  (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T)) (Q : Poly Φ) (Q' : Poly Φ')

theorem le_cover_restrict_compat {c : R'} {a : IdF Φ.A} {a' : IdF Φ'.A} (h : m.LeC c a a') :
    (m1 m E E' e he hρ).LeC c (a.res (Cut.U E)) (a'.res (Cut.U E')) := fun T x hx => h T.T x hx

theorem pull_restrict_first_piece_compat (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (j : ℕ)
    (x : CH.H (sq (a.res (Cut.U E)) (b.res (Cut.U E))) j) :
    (mP m E E' e he hρ Q Q' c ha hb).pull j
        ((CH.Mor.restrict (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q)).pull j x) =
      (CH.Mor.restrict (sq (a'.res (Cut.U E')) (b'.res (Cut.U E'))) (Cut.P0 Q')).pull j
        (((m1 m E E' e he hρ).sqC c (le_cover_restrict_compat m E E' e he hρ ha) (le_cover_restrict_compat m E E' e he hρ hb)).pull j x) := by
  let μ₁ : CH.Mor (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ :=
    (CH.Mor.restrict (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q)).comp (mP m E E' e he hρ Q Q' c ha hb)
  let μ₂ : CH.Mor (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ :=
    ((m1 m E E' e he hρ).sqC c (le_cover_restrict_compat m E E' e he hρ ha) (le_cover_restrict_compat m E E' e he hρ hb)).comp
      (CH.Mor.restrict (sq (a'.res (Cut.U E')) (b'.res (Cut.U E'))) (Cut.P0 Q'))
  have h := CrystallineSemistableComparison.P.prism μ₁ μ₂ (eta m E E' e he hρ Q Q') (fun T x => rfl) j x
  exact (CrystallineSemistableComparison.P.pull_comp _ _ j x).1.symm.trans (h.trans (CrystallineSemistableComparison.P.pull_comp _ _ j x).1)

def alpha {d : ℕ} {E : Frame (Φ := Φ) (d + 1)} (Q : Poly Φ) (a b : IdF Φ.A) : Pt.U E ⋙ sq a b ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq a b :=
  Functor.whiskerRight (Cut.jNat (E := E) Q) (sq a b)

theorem alpha_τ (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (X : Pt E')
    (y : sqM a b (m.G.obj X.T)) :
    (mP m E E' e he hρ Q Q' c ha hb).τ X (((alpha Q a b).app ((Gp m E E' e).obj X)).hom y) =
      ((alpha Q' a' b').app X).hom ((mPt m E E' e c ha hb).τ X y) := by
  change (m.sqC c ha hb).τ (Q'.P X.T) (((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom
      (((sq a b).map (Q.j (m.G.obj X.T))).hom y)) = ((sq a' b').map (Q'.j X.T)).hom ((m.sqC c ha hb).τ X.T y)
  rw [← (m.sqC c ha hb).nat]
  congr 1
  have h2 := congrArg (fun t => ((sq a b).map t).hom y) (j_eta m E E' e he hρ Q Q' X)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

theorem alpha_hom (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (k : ℕ)
    (x : CH.Cn (Pt.U E ⋙ sq a b) k) :
    (mP m E E' e he hρ Q Q' c ha hb).hom.f k ((CH.Mor.ofNatTrans (alpha Q a b)).hom.f k x) =
      (CH.Mor.ofNatTrans (alpha Q' a' b')).hom.f k ((mPt m E E' e c ha hb).hom.f k x) :=
  funext fun s => alpha_τ m E E' e he hρ Q Q' c ha hb _ _

theorem rho_finsupp_sum_dpow (c : R') {T P' : C'} (jj : T ⟶ P') (η : Q.P (m.G.obj T) ⟶ m.G.obj P') (X' : Φ'.A.obj P')
    (hj : Q.j (m.G.obj T) ≫ η = m.G.map jj) (hx : m.ρ P' ((Φ.A.map η).hom (Q.X (m.G.obj T))) = X')
    (cc : ℕ →₀ Φ.A.obj (m.G.obj T)) :
    algebraMap R' (Φ'.A.obj P') c * m.ρ P' ((Φ.A.map η).hom
        (cc.sum fun k y => (Φ.A.map (Q.j (m.G.obj T))).hom y * Φ.dp k (Q.X (m.G.obj T)))) =
      (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj T) c * m.ρ T x) (by simp)).sum
        fun k y => (Φ'.A.map jj).hom y * Φ'.dp k X' := by
  rw [Finsupp.sum_mapRange_index (by intro k; simp), map_finsuppSum, map_finsuppSum, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  have hX := Q.X_mem (m.G.obj T)
  have hX' := Φ.J.map_mem η hX
  have h1 : (Φ.A.map η).hom ((Φ.A.map (Q.j (m.G.obj T))).hom (cc k)) = (Φ.A.map (m.G.map jj)).hom (cc k) := by
    rw [← Cut.mapA_comp, hj]
  rw [map_mul, map_mul, h1, m.nat, Φ.dp_map _ _ hX, m.dp _ _ hX', hx, map_mul, AlgHom.commutes, mul_assoc]

theorem rho_sum (c : R') (X : Pt E') (cc : ℕ →₀ Φ.A.obj (m.G.obj X.T)) :
    algebraMap R' (Φ'.A.obj (Q'.P X.T)) c * m.ρ (Q'.P X.T) ((Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom
        (cc.sum fun k y => (Φ.A.map (Q.j (m.G.obj X.T))).hom y * Φ.dp k (Q.X (m.G.obj X.T)))) =
      (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp)).sum
        fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T) :=
  rho_finsupp_sum_dpow m Q c (Q'.j X.T) (etaC m E E' e he hρ Q Q' X).1 (Q'.X X.T) (j_eta m E E' e he hρ Q Q' X)
    (rho_eta m E E' e he hρ Q Q' X) cc

theorem beta_τ {a b : ℤ → IdF Φ.A} {a' b' : ℤ → IdF Φ'.A} {r : ℤ} (c : R')
    (ha : ∀ r', m.LeC c (a r') (a' r')) (hb : ∀ r', m.LeC c (b r') (b' r'))
    (hca : Q.Crit a r) (hca1 : Q.Crit a (r - 1))
    (β : Cut.P0 Q ⋙ Cut.U E ⋙ sq (a r) (b r) ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq (a (r - 1)) (b (r - 1)))
    (hβ : ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (a r) (b r) (Q.P X.T)) (z' : sqM (a (r - 1)) (b (r - 1)) (Q.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        (β.app X).hom z = z')
    (β' : Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r) (b' r) ⟶ Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' (r - 1)) (b' (r - 1)))
    (hβ' : ∀ (X : Pt E') (c c' : ℕ →₀ Φ'.A.obj X.T) (z : sqM (a' r) (b' r) (Q'.P X.T)) (z' : sqM (a' (r - 1)) (b' (r - 1)) (Q'.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        (β'.app X).hom z = z')
    (X : Pt E') (y : sqM (a r) (b r) (Q.P (m.G.obj X.T))) :
    (mP m E E' e he hρ Q Q' c (ha (r - 1)) (hb (r - 1))).τ X ((β.app ((Gp m E E' e).obj X)).hom y) =
      (β'.app X).hom ((mP m E E' e he hρ Q Q' c (ha r) (hb r)).τ X y) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
  obtain ⟨cc, rfl⟩ := Q.span _ w
  have hmem := (hca (m.G.obj X.T) cc).1 hw
  let c' : ℕ →₀ Φ.A.obj (m.G.obj X.T) := cc.comapDomain (· + 1) (fun _ _ _ _ h => Nat.add_right_cancel h)
  have hc' : ∀ k, c' k = cc (k + 1) := fun k => Finsupp.comapDomain_apply _ _ _ _
  have hw' := (hca1 (m.G.obj X.T) c').2 fun k => by
    rw [hc']
    have h := hmem (k + 1)
    rwa [show r - ((k + 1 : ℕ) : ℤ) = r - 1 - (k : ℤ) by push_cast; ring] at h
  have hb1 := hβ ((Gp m E E' e).obj X) cc c' ⟨_, hy⟩ ⟨_, Ideal.mem_map_of_mem _ hw'⟩ hc' rfl rfl
  rw [hb1]
  symm
  refine hβ' X (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp))
    (c'.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp)) _ _ (fun k => ?_) ?_ ?_
  · rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, hc']
  · exact congrArg (Ideal.Quotient.mk _) (rho_sum m E E' e he hρ Q Q' c X cc)
  · exact congrArg (Ideal.Quotient.mk _) (rho_sum m E E' e he hρ Q Q' c X c')

end Cuts

end GlobalTheory.CompanionTheory.LocBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergence
section
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.RgEisSide

variable {G : Type} [Group G] [TopologicalSpace G]
  {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem one_toIdele_lemma (y : IdeleGroup k) :
    (((1 : HeckeCharacter k).toIdele y : Circle) : ℂ) = 1 := by
  first
  | rfl
  | simp [HeckeCharacter.toIdele]

theorem side_one {π : G →* GL ι 𝔸[k]} {Γ K P : Subgroup G} {i : ι} {ω : HeckeCharacter k}
    {d : ι → IdeleGroup k} {c : G → ℂ} {η : G → ℝ} (hs : Side π Γ K P i ω d c η) :
    Side π Γ K P i (1 : HeckeCharacter k) d (1 : G → ℂ) η := by
  refine ⟨hs.two, mul_one 1, hs.cont, hs.piK, hs.piΓ, hs.trans, hs.mem,
    ⟨hs.par.closed, hs.par.iwa, ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl,
      continuous_one.continuousOn⟩⟩, hs.ht, fun p hp => ⟨?_, (hs.val p hp).2⟩⟩
  exact (one_toIdele_lemma _).symm

theorem norm_globalZeta_le (F : 𝔸[k] → ℂ) (x : ℝ) :
    ‖globalZeta F (1 : HeckeCharacter k) x‖ ≤
      ∫ t : IdeleGroup k, ‖F (t : 𝔸[k])‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ∂ideleMeasure k := by
  unfold GroundTheory.Global.globalZeta
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext t
  rw [norm_mul, norm_mul, one_toIdele_lemma, norm_one, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k t).2, Complex.ofReal_re]

private theorem stab_lemma {R : Type} [CommRing R] (h : GL ι R) (i : ι) (a b : R)
    (h1 : (h : Matrix ι ι R).mulVec (Pi.single i 1) = a • Pi.single i 1)
    (h2 : ((h⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) = b • Pi.single i 1) :
    h ∈ stab R {i} := by
  show ∀ r ∉ ({i} : Set ι), ∀ c ∈ ({i} : Set ι),
    (h : Matrix ι ι R) r c = 0 ∧ ((h⁻¹ : GL ι R) : Matrix ι ι R) r c = 0
  intro r hr c hc
  rw [Set.mem_singleton_iff] at hc hr
  subst hc
  constructor
  · have := congrFun h1 r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hr] using this
  · have := congrFun h2 r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hr] using this

private theorem stab_lemma_2 {R : Type} [CommRing R] (X Y : GL ι R) (i : ι) (c₁ c₂ : Rˣ)
    (h : (c₁ : R) • ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      (c₂ : R) • ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1)) :
    Y * X⁻¹ ∈ stab R {i} := by
  have hX : ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      ((↑c₁⁻¹ : R) * c₂) • ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) := by
    rw [mul_smul, ← h, smul_smul, Units.inv_mul, one_smul]
  have hY : ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      ((↑c₂⁻¹ : R) * c₁) • ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) := by
    rw [mul_smul, h, smul_smul, Units.inv_mul, one_smul]
  apply stab_lemma (Y * X⁻¹) i ((↑c₁⁻¹ : R) * c₂) ((↑c₂⁻¹ : R) * c₁)
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Units.mul_inv, Matrix.one_mulVec]
  · rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private theorem vec_mul_lemma_3 (A B : GL ι 𝔸[k]) (i : ι) :
    vec (A * B) i = ((B⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (vec A i) := by
  unfold PositivityTheory.RgEis.MG.vec
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem sideConv : EpConv → TestSph → Lines → Term → SideConv := by
  intro hEp hTest hLines hTerm
  unfold PositivityTheory.RgEis.MG.SideConv
  intro G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hs x hx
  unfold PositivityTheory.RgEis.Conv
  intro g
  have hs1 := side_one hs
  have hcard : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hs.two
  have hx1 : (1 : ℝ) < x := by linarith
  obtain ⟨Ψ, Ψ₁, hΨ, -, -, hsph, hZ⟩ := hTest k ι i
  obtain ⟨-, hT⟩ := hTerm G K hK k ι π Γ P i 1 d 1 η hs1
  obtain ⟨hline, -, hscale⟩ := hT Ψ (x : ℂ)
  obtain ⟨e, he⟩ := hLines G K hK k ι π Γ P i ω d c η hs
  obtain ⟨-, hconv⟩ := hEp k ι Ψ hΨ
  obtain ⟨u, hu, hub⟩ := hconv x {(π g * dgl d)⁻¹} (max_lt hx1 hx) isCompact_singleton
  have hzt : ∀ κ ∈ K, zt π d i Ψ (1 : HeckeCharacter k) (x : ℂ) κ =
      globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ) := by
    intro κ hκ
    show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) (1 : HeckeCharacter k) (x : ℂ) = _
    congr 1
    funext t
    exact hsph t ⟨kap π d κ, hs.piK κ hκ⟩
  have hA : ∀ q : Cos P Γ,
      ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ =
        Real.exp (x * η (rep q * g)) * (‖modPow (d i) (x : ℂ)‖ *
          ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖) := by
    intro q
    obtain ⟨p, hp, κ, hκ, hpk⟩ := hs.par.iwa (rep q * g)
    have hη : η (p * κ) = η p := by
      rw [hs.ht.left p hp κ]
      have h1 : η κ = η 1 := by simpa using hs.ht.right 1 κ hκ
      rw [h1, hs.ht.rat 1 (one_mem Γ) (one_mem P), add_zero]
    rw [hpk, hline p hp κ hκ, hzt κ hκ, hη, norm_mul, norm_mul, norm_mul, norm_mul,
      one_toIdele_lemma, Pi.one_apply, norm_one, one_mul, one_mul, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal]
  have hApos : 0 < ‖modPow (d i) (x : ℂ)‖ *
      ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖ := by
    refine mul_pos ?_ (norm_pos_iff.mpr (hZ x hx1))
    unfold GroundTheory.Automorphic.GodementSection.modPow
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k (d i)).2]
    exact Real.rpow_pos_of_pos (IdeleGroup.ideleModule k (d i)).2 _
  have hbound : ∀ q : Cos P Γ,
      ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ ≤ u (e q) := by
    intro q
    obtain ⟨a, Ha⟩ := he q
    have hw : vec (π (rep q * g) * dgl d) i =
        (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (vec (π (rep q)) i) := by
      rw [map_mul, mul_assoc, vec_mul_lemma_3]
    rw [← hscale a, hw, ← Matrix.mulVec_smul, ← Ha]
    exact (norm_globalZeta_le (fun t => Ψ (t • (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) :
      Matrix ι ι 𝔸[k]).mulVec (ratV (e q).rep))) x).trans (hub _ rfl (e q))
  have hinj : Function.Injective e := by
    intro q₁ q₂ heq
    obtain ⟨a₁, H₁⟩ := he q₁
    obtain ⟨a₂, H₂⟩ := he q₂
    rw [heq] at H₁
    have key : ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₁ : 𝔸[k]ˣ) : 𝔸[k]) •
        (((π (rep q₁))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i 1) =
        ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₂ : 𝔸[k]ˣ) : 𝔸[k]) •
        (((π (rep q₂))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i 1) :=
      H₁.symm.trans H₂
    have hst := stab_lemma_2 (π (rep q₁)) (π (rep q₂)) i _ _ key
    rw [← map_inv, ← map_mul] at hst
    have hP := (hs.mem _).mpr hst
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr (Subgroup.mem_subgroupOf.mpr hP))
  refine Summable.of_nonneg_of_le (fun q => (Real.exp_pos _).le) (fun q => ?_)
    ((hu.comp_injective hinj).div_const (‖modPow (d i) (x : ℂ)‖ *
      ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖))
  show Real.exp (x * η (rep q * g)) ≤ u (e q) / _
  rw [le_div_iff₀ hApos, ← hA q]
  exact hbound q

end GlobalTheory.CompanionTheory.RgEisSide
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfolding
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.RgEisSide

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem inv_mulVec_smul_vec (m γ : GL ι 𝔸[k]) (x : 𝔸[k]) (i : ι) :
    ((m⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ (x • MG.vec γ i) = x • MG.vec (γ * m) i := by
  unfold MG.vec
  rw [Matrix.mulVec_smul, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]


omit [Fintype ι] [DecidableEq ι] in
theorem norm_lineZeta_le (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (v : ι → 𝔸[k]) :
    ‖lineZeta Ψ ω s v‖ ≤ ∫ t : IdeleGroup k, ‖Ψ ((t : 𝔸[k]) • v)‖ *
      (IdeleGroup.ideleModule k t : ℝ) ^ s.re ∂ideleMeasure k := by
  unfold lineZeta globalZeta
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hpos : (0 : ℝ) < (IdeleGroup.ideleModule k t : ℝ) := (IdeleGroup.ideleModule k t).2
  simp only [norm_mul, Circle.norm_coe, mul_one]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]

section Eis

variable {G : Type} [Group G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem avg_const_mul {K : Subgroup G} [MeasurableSpace K] (μ : Measure K) (ρ : K →* (W →L[ℂ] W)) (a : ℂ) (φ : K → ℂ) :
    avg μ ρ (fun κ => a * φ κ) = a • avg μ ρ φ := by
  unfold avg
  rw [← integral_smul]
  simp only [smul_smul]

theorem eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (a : ℂ) (w : W) :
    eis Γ K P c ρ Λ g (a • w) = a • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  exact tsum_congr fun q => by rw [map_smul, smul_comm]

end Eis

theorem sideUnfold : EpConv → Unfold → Lines → Term → ZetaK → SideUnfold := by
  intro hE hU hL hT hZ G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hP k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ s hs g w
  have hcard : (1 : ℝ) < (Fintype.card ι : ℝ) := by
    have := hS.two
    exact_mod_cast (by omega : 1 < Fintype.card ι)
  have hs1 : 1 < s.re := hcard.trans hs
  obtain ⟨e, he⟩ := hL G K hK k ι π Γ P i ω d c η hS
  obtain ⟨hT1, hT2⟩ := hT G K hK k ι π Γ P i ω d c η hS
  obtain ⟨hTp, hTl, hTx⟩ := hT2 Ψ s
  obtain ⟨-, hZc, -⟩ := hZ G K hK k ι π Γ P i ω d c η hS Ψ hΨ
  set a : ℂ := (ω.toIdele (d i) : ℂ) * modPow (d i) s with ha
  let T : G → ℂ := fun y => lineZeta Ψ ω s (MG.vec (π y * dgl d) i)
  let φ : K → ℂ := fun κ => a * zt π d i Ψ ω s κ
  let Λ : G → ℂ := fun x => s * η x
  have key : ∀ (y : G) (q : Cos P Γ), lineZeta Ψ ω s
      (((π y * dgl d)⁻¹ : GL ι 𝔸[k]).1 *ᵥ ratV (e q).rep) = T (rep q * y) := by
    intro y q
    obtain ⟨x, hx⟩ := he q
    rw [hx, inv_mulVec_smul_vec, hTx]
    simp only [T, map_mul, mul_assoc]
  have hφc : Continuous φ := by
    have h1 : Continuous fun κ : K => zt π d i Ψ ω s κ := by
      have h2 : ContinuousOn (fun y : ℂ × K => zt π d i Ψ ω y.1 y.2) (Set.univ.image fun κ : K => (s, κ)) :=
        hZc.mono (by rintro _ ⟨κ, -, rfl⟩; exact ⟨hs1, Set.mem_univ _⟩)
      have h3 := h2.comp_continuous (f := fun κ : K => (s, κ)) (by fun_prop) (fun κ => ⟨κ, Set.mem_univ _, rfl⟩)
      exact h3
    exact continuous_const.mul h1
  have hφl : Law K P c φ := fun r κ hr => by
    have h : zt π d i Ψ ω s ((r * κ : K) : G) = c r * zt π d i Ψ ω s κ := hTl r κ hr
    simp only [φ]
    rw [h]
    ring
  have hΛ : ∀ x, ∀ κ ∈ K, Λ (x * κ) = Λ x := fun x κ hκ => by
    simp only [Λ, hS.ht.right x κ hκ]
  have hTP : ∀ p ∈ P, ∀ κ : K, T (p * κ) = c p * Complex.exp (Λ p) * φ κ := fun p hp κ =>
    hTp p hp κ κ.2
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hCc : IsCompact (Set.range fun κ : K => ((π (g * κ) * dgl d)⁻¹ : GL ι 𝔸[k])) := by
    refine isCompact_range ?_
    have hπ := hS.cont
    exact ((hπ.comp (continuous_const.mul continuous_subtype_val)).mul continuous_const).inv
  obtain ⟨u, hu, hub⟩ := (hE k ι Ψ hΨ).2 s.re _ (max_lt hs1 hs |>.trans_le le_rfl) hCc
  have hbound : ∀ (q : Cos P Γ) (κ : K), ‖T (rep q * (g * κ))‖ ≤ (u ∘ e) q := fun q κ => by
    rw [← key]
    exact (norm_lineZeta_le Ψ ω s _).trans (hub _ ⟨κ, rfl⟩ (e q))
  have hfun : (fun κ : K => epstein Ψ ω s (π (g * κ) * dgl d)) = fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ)) := by
    funext κ
    unfold epstein
    rw [← e.tsum_eq]
    exact tsum_congr fun q => key _ q
  have hmain := hU G W K ρ hK hρ μ hμ hP Γ P c hS.par φ Λ T hφc hφl hΛ hTP g (u ∘ e) (e.summable_iff.2 hu) hbound w
  rw [hfun, hmain]
  simp only [φ]
  rw [avg_const_mul, _root_.smul_apply, eis_smul]

end GlobalTheory.CompanionTheory.RgEisSide
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntSmul
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.He2M1

theorem thetaC_smul {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) :
    thetaC (c • F) h = c * thetaC F h := by
  unfold thetaC
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem thetaCInt_smul : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) (c : ℂ) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}), thetaCInt w (c • F) ω t = c * thetaCInt w F ω t := by
  intro k _ _ ι _ _ w c F ω t
  unfold thetaCInt
  simp only [thetaC_smul, mul_assoc]
  exact integral_const_mul c _

end GlobalTheory.CompanionTheory.He2M1
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VolCharOneEq
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinVol

theorem volChar_one_eq {k : Type} [Field k] [NumberField k] :
    ∃ V : ℝ, 0 < V ∧ volChar (1 : HeckeCharacter k) = (V : ℂ) := by
  haveI := GroundTheory.Global.isHaarMeasure_normOneMeasure k
  haveI : Countable ↥(GroundTheory.Global.diagonalNormOne k).op := by
    haveI := GroundTheory.Global.countable_diagonalNormOne k
    refine Function.Injective.countable (f := fun x : ↥(GroundTheory.Global.diagonalNormOne k).op =>
      (⟨x.1.unop, Subgroup.mem_op.mp x.2⟩ : ↥(GroundTheory.Global.diagonalNormOne k))) ?_
    intro x y h
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact congrArg Subtype.val h
  have hfin : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) < ⊤ :=
    GroundTheory.Global.normOneMeasure_normOneFundamentalDomain_lt_top k
  have hne : GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k) ≠ 0 :=
    (GroundTheory.Global.isFundamentalDomain_normOneFundamentalDomain k
      (GroundTheory.Global.normOneMeasure k)).measure_ne_zero (NeZero.ne _)
  refine ⟨(GroundTheory.Global.normOneMeasure k (GroundTheory.Global.normOneFundamentalDomain k)).toReal,
    ENNReal.toReal_pos hne hfin.ne, ?_⟩
  have h2 : volChar (1 : HeckeCharacter k) =
      ∫ _u in GroundTheory.Global.normOneFundamentalDomain k, (1 : ℂ) ∂GroundTheory.Global.normOneMeasure k := by
    unfold volChar
    congr 1
  rw [h2, MeasureTheory.setIntegral_const]
  simp [Measure.real]

end GlobalTheory.CompanionTheory.EpsteinVol
end

