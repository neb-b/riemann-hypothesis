module

public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.ColSpanMulUnit

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypTwA
section
noncomputable section

namespace Formalism.MainNotions.G.ChF

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.G.Cmp Formalism.L2.G Formalism.L2.G.RelativeIndexFlags
open scoped TensorProduct

theorem det_mem_sub {K : Type} [CommRing K] (O : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (h : ∀ a b, A a b ∈ O) :
    A.det ∈ O := by
  rw [Matrix.det_apply]
  refine Subring.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (Subring.prod_mem _ fun a _ => h _ _) _

def unitsOf {K : Type} [CommRing K] (O : Subring K) : Subgroup Kˣ where
  carrier := {z | (z : K) ∈ O ∧ ((z⁻¹ : Kˣ) : K) ∈ O}
  one_mem' := ⟨O.one_mem, by rw [inv_one]; exact O.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨O.mul_mem ha hb, by rw [_root_.mul_inv_rev]; exact O.mul_mem hb' ha'⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨ha', by rw [inv_inv]; exact ha⟩

theorem det_mem_unitsOf {K : Type} [CommRing K] (O : Subring K) {n : ℕ} (g : GL (Fin n) K)
    (h : ∀ a b, (g : Matrix (Fin n) (Fin n) K) a b ∈ O) (h' : ∀ a b, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ O) :
    Matrix.GeneralLinearGroup.det g ∈ unitsOf O :=
  ⟨det_mem_sub O _ h, by rw [← map_inv]; exact det_mem_sub O _ h'⟩

theorem det_bc {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (g : GL (Fin n) A) :
    Matrix.GeneralLinearGroup.det (bc φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  apply Units.ext
  exact (RingHom.map_det φ (g : Matrix (Fin n) (Fin n) A)).symm

theorem quot_calc {Q : Type} [CommGroup Q] (U : Subgroup Q) (Y dB dB' dg dk : Q) (b k : ℕ)
    (h1 : dB'⁻¹ * Y * dB ∈ U) (h2 : dB'⁻¹ * (Y * dk) * dB ∈ U) (h : Y ^ (b + k) = dg * Y ^ b * dk) :
    (dB' * dB⁻¹) ^ k * dg⁻¹ ∈ U := by
  have hk : dk ∈ U := by
    have e0 : dB'⁻¹ * (Y * dk) * dB = dB'⁻¹ * Y * dB * dk := by ac_rfl
    have e : dk = (dB'⁻¹ * Y * dB)⁻¹ * (dB'⁻¹ * (Y * dk) * dB) := by
      rw [e0, inv_mul_cancel_left]
    rw [e]
    exact U.mul_mem (U.inv_mem h1) h2
  have hY : Y ^ k = dg * dk := by
    rw [pow_add, mul_comm dg, mul_assoc] at h
    exact mul_left_cancel h
  have e : (dB' * dB⁻¹) ^ k * dg⁻¹ = ((dB'⁻¹ * Y * dB) ^ k)⁻¹ * dk := by
    have e1 : dB'⁻¹ * Y * dB = (dB' * dB⁻¹)⁻¹ * Y := by
      rw [mul_inv, inv_inv]
      ac_rfl
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = dB' * dB⁻¹ := ⟨_, rfl⟩
    rw [← hZ] at e1 ⊢
    rw [e1, mul_pow, inv_pow, hY]
    generalize Z ^ k = z
    rw [mul_inv, inv_inv, mul_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  rw [e]
  exact U.mul_mem (U.inv_mem (U.pow_mem h1 k)) hk

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {p : ℕ} {G : GAtP p}

def epsU (B B' γ : GL (Fin n) E) (k : ℕ) : Eˣ :=
  (Matrix.GeneralLinearGroup.det B' * (Matrix.GeneralLinearGroup.det B)⁻¹) ^ k * (Matrix.GeneralLinearGroup.det γ)⁻¹


set_option maxHeartbeats 1000000 in
theorem epsU_ph (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) (hp : p.Prime) (hT : ¬ p ∣ T)
    (halg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (hb : ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 S.Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, (((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)).mulVec t a ∈ (A.pl v).1.adicCompletionIntegers F)
    (Lc : Submodule (𝓞 E) (Fin n → E)) (y : UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ x, x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F Lc ↔
      ((y.1⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.hat F S.Lb)
    (hle : ∀ x ∈ Lc, x ∈ dualSet (σ : E →+* E) J Lc)
    (B' : GL (Fin n) E) (hB' : IsLocBasis p (dualSet (σ : E →+* E) J Lc) B')
    (γ : GL (Fin n) E) (κ : S.U) (b k : ℕ)
    (h : y.1 ^ (b + k) = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y.1 ^ b * κ.1) (v : Fin G.P.nV) :
    Units.map (A.phE v).toMonoidHom (epsU A.B B' γ k) ∈ unitsOf ((A.pl v).1.adicCompletionIntegers F).toSubring := by
  have key : ∀ κ' : S.U, (Matrix.GeneralLinearGroup.det (bc (A.phE v) B'))⁻¹ *
      Matrix.GeneralLinearGroup.det (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1))) *
      Matrix.GeneralLinearGroup.det (bc (A.phE v) A.B) ∈ unitsOf ((A.pl v).1.adicCompletionIntegers F).toSubring := by
    intro κ'
    obtain ⟨h1, h2⟩ := int_of_move (A.pl v).1 (A.spl v) (halg v) A.B B' (hb v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1))
      ((loc_facts S (A.pl v).1 hp (A.pl v).2 hT Lc y hy hle B' hB').2 κ')
    have h3 := det_mem_unitsOf ((A.pl v).1.adicCompletionIntegers F).toSubring
      ((bc (A.phE v) B')⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1)) * bc (A.phE v) A.B) h1 (by
        have e : ((bc (A.phE v) B')⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1)) * bc (A.phE v) A.B)⁻¹ =
            (bc (A.phE v) A.B)⁻¹ * (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (y.1 * κ'.1)))⁻¹ * bc (A.phE v) B' := by group
        rw [e]
        exact h2)
    rwa [map_mul, map_mul, map_inv] at h3
  have k1 := key 1
  have k2 := key κ
  rw [show ((1 : S.U) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1 from rfl, mul_one] at k1
  rw [map_mul, map_mul, map_mul] at k2
  have h' := congrArg (fun z => Matrix.GeneralLinearGroup.det (bc (A.ph v) (bc (prV (E := E) (A.pl v).1) z))) h
  simp only [map_mul, map_pow, bc_ph_incl] at h'
  have := quot_calc _ _ _ _ _ _ b k k1 k2 h'
  rw [det_bc, det_bc, det_bc] at this
  rw [epsU, map_mul, map_pow, map_mul, map_inv, map_inv]
  exact this

end Gen

end Formalism.MainNotions.G.ChF

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ChartRank.HypVin
section
noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PValIntN

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem le_dual_chart {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type}
    {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) (c : cl) :
    ∀ x ∈ lat c, x ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (lat c) := by
  intro x hx x' hx'
  have hglob : ∀ z ∈ lat c, z ∈ Formalism.UG.CS.globLat (K.y c).1 K.lev.Lb := by
    intro z hz
    exact (K.y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ K.lev.Lb, ∀ b ∈ K.lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := K.lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) K.lev.Lb 1 hm (K.y c).1
    (K.y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwL_descent _ _ _ h


open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB in
theorem exB_of_lat {i : ℕ} (hi : i ≤ D.R.m) (q : ℕ) [Fact q.Prime] (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E))
    (hL : Submodule.IsFullLattice D.host.E L) :
    ∃ B' : GL (Fin (D.R.N i)) D.host.E, IsLocBasis q (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) L) B' := by
  obtain ⟨d, hd, hle⟩ := dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hL
  have hsp := dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) _ hL.toIsLattice
  obtain ⟨B, hB⟩ := exists_isLocBasis q _ _ (fg_of_le_bnd hd hle) hsp
  refine ⟨B, ?_⟩
  have e : ((Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) L) :
      Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
      dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) L := span_dualSet _ _ _
  rwa [e] at hB

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ}
  {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

structure LatIn (S : StepIn M i hi G) (w : D.what₂.places.Pl) (β : S.Ch) : Prop where
  prime : p.Prime
  resChar : D.what₂.places.resChar w = p
  siteGood_prime_torsion : ¬ p ∣ S.T
  alg : ∀ v (a : ((S.loc β).pl v).1.adicCompletion D.host.F),
    (S.loc β).spl v ((1 : D.host.E) ⊗ₜ[D.host.F] a) = (a, a)
  base : ∀ v (t : Fin (D.R.N i) → ((S.loc β).pl v).1.adicCompletion D.host.F),
    (∃ x ∈ Formalism.L2.Herm.locL ((S.loc β).pl v).1 (S.K β).lev.Lb, ∀ a, ((S.loc β).spl v (x a)).1 = t a) ↔
      ∀ a, (((bc ((S.loc β).phE v) (S.loc β).B)⁻¹ : GL (Fin (D.R.N i)) (((S.loc β).pl v).1.adicCompletion D.host.F)) :
        Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) _).mulVec t a ∈ ((S.loc β).pl v).1.adicCompletionIntegers D.host.F
  lat : ∀ cl : {c // S.chOf c = β}, Submodule.IsFullLattice D.host.E (S.lat cl.1)
  chi : ∀ κ : (S.K β).lev.U, ∃ r ∈ intW D.what₂.places w, r⁻¹ ∈ intW D.what₂.places w ∧
    D.what₂.embLL r = ((S.K β).lev.chi κ : ℂ)


set_option maxHeartbeats 8000000 in
theorem valIntN_of (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (w : D.what₂.places.Pl)
    (H : ∀ β, S.Core e β) (hS : BlockRationalityField) (hfrac : IsFractionRing G.O G.Kf)
    (hR0 : ∀ x, x ∈ intW D.what₂.places w ↔ e x ∈ Set.range (algebraMap G.O G.Kf))
    (L : ∀ β, LatIn S w β) : S.ValIntN e w := by
  intro β
  have hp := (L β).prime
  have hpw := (L β).resChar
  subst hpw
  have : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  have hblk : BlockRational G.P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D))
      (crdB (embT D) (S.loc β).B) D.what₂.embLL (M.lam i) := by
    refine hS G.P (S.loc β).rk S.pos _ _ D.what₂.embLL (M.lam i) (H β).wt fun τ => ⟨bc (tEL D τ) ((S.loc β).B)⁻¹, ?_⟩
    ext a b
    exact (tEL_emb D τ _).symm
  exact valIntAt_of (S := (S.K β).lev) (emb := embT D) (embLL := D.what₂.embLL) (G := S.charts.gat β)
    (e := e) (A := S.loc β) (pos := S.pos) (embV := S.embN β) (yc := (S.K β).y) weylLatticeDescent_holds hfrac (tEL D) (tEL_emb D)
    (intW D.what₂.places w) hR0 (M.lam i) (H β).wt (valEx_of_rep' (tEL D) (tEL_emb D) (embT_conj D) (H β).std (S.adExt β)
      (ptEx_of (H β).good (S.K β).lev (S.K β).y (S.K β).y_bij.2)
      (ptOne_of (S.K β).lev (H β).int (H β).hypP (H β).bad_p)
      (S.evRatRep β (H β).chRat hblk) (H β).chiRat)
    (fun cl B' => IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (S.lat cl.1)) B')
    (fun cl => exB_of_lat hi (D.what₂.places.resChar w) (S.lat cl.1) ((L β).lat cl))
    (fun a Lt cl g γ κ hg hγ hpt B' hB' v s => by
      exact latO_of (tEL D) (H β).pos_emb
        (fun x => by rw [Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.host_conj_involutive])
        (H β).std γ hγ B' Lt
        (fun v => by
          rw [hg v]
          exact latW_gen (S.K β).lev (S.loc β) (H β).int hp (L β).siteGood_prime_torsion (L β).alg (L β).base (S.lat cl.1) ((S.K β).y cl)
            ((S.K β).y_lat cl) (le_dual_chart (S.K β) cl) B' hB' a g γ κ hpt v)
        (fun v a b => gramW_gen (S.K β).lev (S.loc β) (H β).int hp (L β).siteGood_prime_torsion (L β).alg
          (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) (S.lat cl.1) ((S.K β).y cl) ((S.K β).y_lat cl) (le_dual_chart (S.K β) cl)
          B' hB' v a b) v s)
    (L β).chi

end Formalism.MainNotions.G.CmpJ.PValIntN

end
end

