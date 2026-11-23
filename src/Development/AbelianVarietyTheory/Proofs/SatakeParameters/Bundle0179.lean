module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0173
public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.SplitEigen

theorem exists_eigen_of_mem_iSup {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U]
    [Module ℂ U] (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible)
    (f : ι → U →ₗ[ℂ] V) (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Set G) (c : G → ℂ) (φ : V) (h0 : φ ≠ 0)
    (hK : ∀ k ∈ K, ρ k φ = c k • φ) (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) :
    ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = c k • v := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ k ∈ K, σ k v = c k • v := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun k hk => ?_⟩
        have h4 : σ k v - c k • v ∈ W.comap (f i) := by
          have h5 := hK k hk
          rw [← e, map_add (f := _)] at h5
          have h6 : f i (σ k v - c k • v) = c k • x - ρ k x := by
            rw [map_sub, hf, map_smul]; rw [smul_add] at h5; linear_combination (norm := module) h5
          rw [Submodule.mem_comap, h6]
          exact sub_mem (W.smul_mem _ hx) (hW k x hx)
        rw [hc, Submodule.mem_bot] at h4
        exact sub_eq_zero.1 h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _), ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

theorem exists_locComp_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ w, IsSplitAt w → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion E))) → ∀ (χ : J →* ℂˣ) (φ : UA E n → ℂ), φ ∈ U → φ ≠ 0 → (∀ x ∈ locU n w, ∀ hx : cLoc w x ∈ J, RU E n x φ = (χ ⟨_, hx⟩ : ℂ) • φ) → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ ∃ v : σ.V, v ≠ 0 ∧ ∀ g : J, σ.ρ g v = (χ g : ℂ) • v := by
  classical
  intro E _ _ _ n U hU w hw J _ _ χ φ hφ h0 hχ
  let π : AutSub E n := ⟨U, hU⟩
  obtain ⟨σ, -, hσ, -⟩ := GlobalTheory.DefU.exists_locComp_split E n π w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨r, -, -, hr2⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have hcl : ∀ g, cLoc w ((e.symm g : locU n w) : UA E n) = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let p : locU n w →* GL (Fin n) (w.adicCompletion E) := (cLoc w).comp (locU n w).subtype
  have hp : p = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  let σ' : Representation ℂ (locU n w) σ.V := σ.ρ.comp p
  have hirr : σ'.IsIrreducible := by
    change Representation.IsIrreducible (σ.ρ.comp p); rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ.ρ e.toMulEquiv σ.irred
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨-, f, hf0, hfm, hf⟩ := hσ
  let F : σ'.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict π.V hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have hsup := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π.V σ.V σ.V π.rep (locU n w).subtype
    σ' σ' π.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0).1
  let c : locU n w → ℂ := fun k => if h : cLoc w (k : UA E n) ∈ J then (χ ⟨_, h⟩ : ℂ) else 0
  obtain ⟨v, hv0, hv⟩ := exists_eigen_of_mem_iSup (π.rep.comp (locU n w).subtype) σ' hirr
    (fun h : σ'.IntertwiningMap (π.rep.comp (locU n w).subtype) => h.toLinearMap)
    (fun h g u => LinearMap.congr_fun (h.isIntertwining' g) u)
    {k | cLoc w (k : UA E n) ∈ J} c ⟨φ, hφ⟩
    (fun h => h0 (congrArg Subtype.val h))
    (fun k hk => Subtype.ext (by
      change RU E n (k : UA E n) φ = c k • φ
      show RU E n (k : UA E n) φ = (if h : cLoc w (k : UA E n) ∈ J then (χ ⟨_, h⟩ : ℂ) else 0) • φ
      have hk' : cLoc w (k : UA E n) ∈ J := hk
      rw [dif_pos hk']
      exact hχ _ k.2 hk'))
    (hsup ▸ Submodule.mem_top)
  refine ⟨v, hv0, fun g => ?_⟩
  have hk : cLoc w ((e.symm g : locU n w) : UA E n) ∈ J := by rw [hcl]; exact g.2
  have h1 := hv (e.symm g) hk
  have h2 : σ' (e.symm g) = σ.ρ g := by
    change σ.ρ (cLoc w ((e.symm g : locU n w) : UA E n)) = _
    rw [hcl]
  rw [h2] at h1
  rw [h1]
  simp only [c, dif_pos hk]
  congr 3
  exact Subtype.ext (hcl g)

end GlobalTheory.SplitEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusLiftMovesLetterCoordinates
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord.FrobMove

theorem inv_map_field {E K : Type*} [Field E] [Field K] (f : E →+* K) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n E) : (M.map f)⁻¹ = M⁻¹.map f := by
  have hd : (M.map f).det = f M.det := (RingHom.map_det f M).symm
  have ha : (M.map f).adjugate = M.adjugate.map f := (RingHom.map_adjugate f M).symm
  rw [Matrix.inv_def, Matrix.inv_def, hd, ha]
  ext i j
  simp [Ring.inverse_eq_inv', map_inv₀]

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

theorem frob_moves_coords : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∀ z a b₀ i, σ (gK D lam P P' b z a b₀ i) = hK D lam P P' b (posPl D p z 1) a b₀ i) ∧ (∀ w a b₀ i, σ (hK D lam P P' b w a b₀ i) = gK D lam P P' b (posPl D p w 1) a b₀ i) := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b
  choose ρ hρ using fun z => exists_ringHom_rhoK D lam σ hσ hcl z
  have hfun : ∀ z, rhoK D lam z = ⇑(ρ z) := fun z => funext fun y => (hρ z y).1
  have hs : ∀ z y, σ (ρ z y) = ρ (posPl D p z 1) (D.host.conj y) := fun z y => by
    rw [← (hρ z y).1, ← (hρ _ _).1]; exact sigma_rhoK D lam σ hσ hcl z y
  have hsm : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E),
      (Q.map (ρ z)).map σ = (Q.map D.host.conj).map (ρ (posPl D p z 1)) := fun z Q => by
    ext i j; simp [hs]
  have hinv : ∀ {n : ℕ} z (Q : Matrix (Fin n) (Fin n) D.host.E) i j,
      σ ((Q.map (ρ z))⁻¹ i j) = ((Q.map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ i j := fun z Q i j => by
    rw [← hsm, inv_map_field σ]; rfl
  have K : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) = 1 := by
    intro n Q hQ z
    have e : ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose *
        ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        ((((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z)).map
          (D.host.conj : D.host.E →+* D.host.E)).map (ρ (posPl D p z 1)) := by
      rw [Matrix.map_mul, Matrix.map_mul]
      congr 1
      ext i j
      simp [conj_conj]
    rw [e, hQ z]
    simp
  have K1 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      (((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)))⁻¹ =
        ((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1))).transpose := fun Q hQ z =>
    Matrix.inv_eq_left_inv (K Q hQ z)
  have K2 : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E),
      (∀ z, ((Q (tauPl D (posPl D p z 1))).map D.host.conj).transpose * Q (tauPl D z) = 1) → ∀ z,
      ((Q (tauPl D z)).map D.host.conj).map (ρ (posPl D p z 1)) =
        (((Q (tauPl D (posPl D p z 1))).map (ρ (posPl D p z 1)))⁻¹).transpose := fun Q hQ z => by
    rw [Matrix.transpose_nonsing_inv]; exact (Matrix.inv_eq_right_inv (K Q hQ z)).symm
  have hPc := hP.2.1 hcl
  have hP'c := hP'.2.1 hcl
  refine ⟨fun z a b₀ i => ?_, fun w a b₀ i => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [gK, hK, hfun, map_sum, map_mul]
      refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
      rw [hs, hs, conj_conj, hinv, K1 P hPc z]
      have e2 := congrFun (congrFun (K2 P' hP'c z) b₁) b₀
      simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
      rw [e2]; ring
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [gK, hK, hfun, map_sum, map_mul]
      refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun a₁ _ => ?_
      rw [hs, hs, hinv, K1 P' hP'c w]
      have e2 := congrFun (congrFun (K2 P hPc w) a₁) a
      simp only [Matrix.map_apply, Matrix.transpose_apply] at e2 ⊢
      rw [e2]; ring

end GlobalTheory.KerStd.HypCoord.FrobMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesDual
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem posPl_inj_lt (D : D7) (p : ℕ) (z : OrbitPlaces.Pl D) {a b : ℕ} (hab : a ≤ b) (hb : b < nP D p)
    (he : posPl D p z a = posPl D p z b) : a = b := by
  have h1 : posPl D p (posPl D p z a) (b - a) = posPl D p z a := by
    rw [posPl_add, Nat.add_sub_cancel' hab, he]
  have hd := posPl_fix D p _ _ h1
  have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

theorem orbMap_inj (D : D7) (p : ℕ) (z : OrbitPlaces.Pl D) {s s' : ZMod (nP D p)}
    (he : posPl D p z s.val = posPl D p z s'.val) : s = s' := by
  apply ZMod.val_injective
  rcases le_total s.val s'.val with h | h
  · exact posPl_inj_lt D p z h (ZMod.val_lt _) he
  · exact (posPl_inj_lt D p z h (ZMod.val_lt _) he.symm).symm

theorem iterate_mul_ringHom {K : Type*} [Semiring K] (σ : K →+* K) (m : ℕ) (x y : K) :
    σ^[m] (x * y) = σ^[m] x * σ^[m] y := by
  rw [← RingHom.coe_pow, map_mul]

theorem fOf_fOf'_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → TrDual (nP D p) σ om oms → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → ∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf' D p σ oms R g e' i = if e = e' then 1 else 0 := by
  intro D p _ σ om oms R N N' r g h hOK hR hTr hσg hpair e e'
  obtain ⟨⟨⟨r0, hr0⟩, k⟩, a, b⟩ := e
  obtain ⟨⟨⟨r1, hr1⟩, k'⟩, a', b'⟩ := e'
  obtain ⟨m, hm⟩ := hOK.even
  have hn2 := hOK.two
  have hval : ∀ t : ZMod (nP D p), t.val % 2 = 0 → (t + 1).val = t.val + 1 := by
    intro t ht
    have hlt := ZMod.val_lt t
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (show 1 < nP D p by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have reps : ∀ (m0 m1 : ℕ), posPl D p r0 m0 = posPl D p r1 m1 → r0 = r1 := fun m0 m1 he =>
    (hR (posPl D p r1 m1)).unique ⟨hr0, m0, he⟩ ⟨hr1, m1, rfl⟩
  have hf : ∀ i, σ (fOf D p σ om R g ((⟨r0, hr0⟩, k), a, b) i) = ∑ t : ZMod (nP D p),
      (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) * h (posPl D p r0 (t.val + 1)) a b i := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fOf, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs with ht
    · rw [map_mul, hσg, ← Function.iterate_succ_apply' σ, OrbitPlaces.orbMap, posPl_add]
    · simp
  have hf' : ∀ i, fOf' D p σ oms R g ((⟨r1, hr1⟩, k'), a', b') i = ∑ t : ZMod (nP D p),
      (if t.val % 2 = 0 then 0 else σ^[t.val] (oms k')) * g (posPl D p r1 t.val) a' b' i := by
    intro i
    simp only [fOf', OrbitPlaces.orbMap]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp
  have h2 : ∑ i, σ (fOf D p σ om R g ((⟨r0, hr0⟩, k), a, b) i) * fOf' D p σ oms R g ((⟨r1, hr1⟩, k'), a', b') i =
      ∑ t : ZMod (nP D p), ∑ t' : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) *
        (if t'.val % 2 = 0 then 0 else σ^[t'.val] (oms k')) *
        (if posPl D p r0 (t.val + 1) = posPl D p r1 t'.val ∧ a = a' ∧ b = b' then 1 else 0) := by
    rw [Finset.sum_congr rfl fun i _ => by rw [hf i, hf' i, Finset.sum_mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [← hpair, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have key : ∀ t t' : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k) else 0) *
        (if t'.val % 2 = 0 then 0 else σ^[t'.val] (oms k')) *
        (if posPl D p r0 (t.val + 1) = posPl D p r1 t'.val ∧ a = a' ∧ b = b' then 1 else 0) =
      if t' = t + 1 then (if t.val % 2 = 0 then σ^[t.val + 1] (om k * oms k') else 0) *
        (if r0 = r1 ∧ a = a' ∧ b = b' then 1 else 0) else 0 := by
    intro t t'
    by_cases ht : t.val % 2 = 0
    · have h1 := hval t ht
      by_cases htt : t' = t + 1
      · subst htt
        have hodd : ¬ (t.val + 1) % 2 = 0 := by omega
        rw [if_pos rfl, h1, if_pos ht, if_pos ht, if_neg hodd, iterate_mul_ringHom]
        by_cases hc : r0 = r1 ∧ a = a' ∧ b = b'
        · obtain ⟨rfl, rfl, rfl⟩ := hc
          simp
        · rw [if_neg hc, if_neg]
          rintro ⟨hp, ha, hb⟩
          exact hc ⟨reps _ _ hp, ha, hb⟩
      · rw [if_neg htt]
        by_cases ht' : t'.val % 2 = 0
        · simp [ht']
        · by_cases hc : posPl D p r0 (t.val + 1) = posPl D p r1 t'.val
          · exfalso
            have hr := reps _ _ hc
            subst hr
            rw [← h1] at hc
            exact htt (orbMap_inj D p r0 hc).symm
          · simp [hc]
    · simp [ht]
  rw [h2, Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => key t t']
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul]
  have h3 : ∑ t : ZMod (nP D p), (if t.val % 2 = 0 then σ^[t.val + 1] (om k * oms k') else 0) =
      σ (∑ t : ZMod (nP D p), if t.val % 2 = 0 then σ^[t.val] (om k * oms k') else 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · rw [Function.iterate_succ_apply']
    · simp
  rw [h3, hTr.2 k k']
  by_cases hk : k = k' <;> by_cases hr : r0 = r1 <;> by_cases ha : a = a' <;> by_cases hb : b = b' <;>
    simp [hk, hr, ha, hb]

end GlobalTheory.KerStd.HypCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIntegralSigmaSqFixed
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem norm_iterate_le_one {p : ℕ} [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (hσ : ∀ x : MaximalUnramifiedExtension p, ‖x‖ ≤ 1 → ‖σ x‖ ≤ 1) (x : MaximalUnramifiedExtension p) (hx : ‖x‖ ≤ 1) (k : ℕ) : ‖σ^[k] x‖ ≤ 1 := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact hσ _ ih

theorem val_add_two_eq (D : D7) (p : ℕ) (t : ZMod (nP D p)) : (t + 2).val = (t.val + 2) % nP D p := by
  have : t + 2 = ((t.val + 2 : ℕ) : ZMod (nP D p)) := by push_cast; simp [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast]

theorem val_add_two_mod_two (D : D7) (p : ℕ) (hO : OrbitPlaces.OrbOK D p) (t : ZMod (nP D p)) :
    (t + 2).val % 2 = t.val % 2 := by
  have h2 : (2 : ℕ) ∣ nP D p := even_iff_two_dvd.mp hO.even
  rw [val_add_two_eq, Nat.mod_mod_of_dvd _ h2]
  omega

theorem sigma_sq_term (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (c : MaximalUnramifiedExtension p)
    (hc : σ^[nP D p] c = c) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hg : ∀ z a b i, σ (σ (g z a b i)) = g (posPl D p z 2) a b i) (z : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N')
    (i : Fin r) (t : ZMod (nP D p)) :
    σ (σ (σ^[t.val] c * g (OrbitPlaces.orbMap D p z t) a b i)) =
      σ^[(t + 2).val] c * g (OrbitPlaces.orbMap D p z (t + 2)) a b i := by
  rw [map_mul, map_mul, hg]
  simp only [OrbitPlaces.orbMap]
  rw [val_add_two_eq, posPl_mod, posPl_add]
  congr 1
  rw [(show Function.IsPeriodicPt σ (nP D p) c from hc).iterate_mod_apply,
    Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem sigma_sq_sum_shift (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (F : ZMod (nP D p) → MaximalUnramifiedExtension p) (hF : ∀ t, σ (σ (F t)) = F (t + 2)) :
    σ (σ (∑ t, F t)) = ∑ t, F t := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  simp_rw [hF]
  exact Fintype.sum_equiv (Equiv.addRight 2) _ _ (fun _ => rfl)

theorem fOf_integral_sigma_sq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → (∀ x : MaximalUnramifiedExtension p, ‖x‖ ≤ 1 → ‖σ x‖ ≤ 1) → OwOK (nP D p) σ om oms → (∀ z a b i, ‖g z a b i‖ ≤ 1) → (∀ z a b i, σ (σ (g z a b i)) = g (posPl D p z 2) a b i) → (∀ e i, ‖fOf D p σ om R g e i‖ ≤ 1 ∧ σ (σ (fOf D p σ om R g e i)) = fOf D p σ om R g e i) ∧ (∀ e i, ‖fOf' D p σ oms R g e i‖ ≤ 1 ∧ σ (σ (fOf' D p σ oms R g e i)) = fOf' D p σ oms R g e i) := by
  intro D p _ σ om oms R N N' r g hO hσ hw hgn hg
  have hterm : ∀ (c : MaximalUnramifiedExtension p), ‖c‖ ≤ 1 → ∀ (z : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N') (i : Fin r) (t : ZMod (nP D p)),
      ‖σ^[t.val] c * g (OrbitPlaces.orbMap D p z t) a b i‖ ≤ 1 := by
    intro c hc z a b i t
    rw [norm_mul]
    exact mul_le_one₀ (norm_iterate_le_one σ hσ c hc _) (norm_nonneg _) (hgn _ _ _ _)
  refine ⟨fun e i => ⟨?_, ?_⟩, fun e i => ⟨?_, ?_⟩⟩
  · unfold fOf
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun t _ => ?_
    split_ifs
    · exact hterm _ (hw.1 _).1 _ _ _ _ _
    · simp
  · unfold fOf
    refine sigma_sq_sum_shift D p σ _ fun t => ?_
    rw [val_add_two_mod_two D p hO t]
    split_ifs
    · exact sigma_sq_term D p σ _ (hw.2 _).1 g hg _ _ _ _ t
    · simp
  · unfold fOf'
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun t _ => ?_
    split_ifs
    · simp
    · exact hterm _ (hw.1 _).2 _ _ _ _ _
  · unfold fOf'
    refine sigma_sq_sum_shift D p σ _ fun t => ?_
    rw [val_add_two_mod_two D p hO t]
    split_ifs
    · simp
    · exact sigma_sq_term D p σ _ (hw.2 _).2 g hg _ _ _ _ t

end GlobalTheory.KerStd.HypCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicCoordinatesIsotropic
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord

theorem posPl_succ_ne_of_parity (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hev : Even (nP D p))
    (hR : OrbitPlaces.IsReps D p R) {r r' : OrbitPlaces.Pl D} (hr : r ∈ R) (hr' : r' ∈ R) {s s' : ℕ}
    (hs : s < nP D p) (hs' : s' < nP D p) (hpar : s % 2 = s' % 2) :
    posPl D p (posPl D p r s) 1 ≠ posPl D p r' s' := by
  intro h
  rw [posPl_add] at h
  have hrr : r = r' :=
    (hR (posPl D p r' s')).unique ⟨hr, s + 1, h⟩ ⟨hr', s', rfl⟩
  subst hrr
  have hpos : 0 < nP D p := by omega
  have h2 : posPl D p r ((s + 1) % nP D p) = posPl D p r s' := by rw [posPl_mod, h]
  have h3 : (s + 1) % nP D p = s' := posPl_inj D p r _ _ (Nat.mod_lt _ hpos) hs' h2
  obtain ⟨m, hm⟩ := hev
  rcases Nat.lt_or_ge (s + 1) (nP D p) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h3
    omega
  · have hsn : s + 1 = nP D p := by omega
    rw [hsn, Nat.mod_self] at h3
    omega

theorem sum_sigma_comb_mul_comb (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' n : ℕ} (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin n → MaximalUnramifiedExtension p)
    (hev : Even (nP D p)) (hR : OrbitPlaces.IsReps D p R)
    (hg : ∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i)
    (hp : ∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0)
    {r r' : OrbitPlaces.Pl D} (hr : r ∈ R) (hr' : r' ∈ R) (a a' : Fin N) (b b' : Fin N')
    (c c' : ZMod (nP D p) → MaximalUnramifiedExtension p) (q : ℕ)
    (hc : ∀ t, t.val % 2 ≠ q → c t = 0) (hc' : ∀ t, t.val % 2 ≠ q → c' t = 0) :
    ∑ i, σ (∑ t, c t * g (OrbitPlaces.orbMap D p r t) a b i) * ∑ t, c' t * g (OrbitPlaces.orbMap D p r' t) a' b' i = 0 := by
  have hterm : ∀ t t' : ZMod (nP D p),
      ∑ i, (σ (c t) * h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i) *
        (c' t' * g (OrbitPlaces.orbMap D p r' t') a' b' i) = 0 := by
    intro t t'
    by_cases h1 : t.val % 2 = q
    · by_cases h2 : t'.val % 2 = q
      · have hne : posPl D p (OrbitPlaces.orbMap D p r t) 1 ≠ OrbitPlaces.orbMap D p r' t' :=
          posPl_succ_ne_of_parity D p R hev hR hr hr' (ZMod.val_lt t) (ZMod.val_lt t') (h1.trans h2.symm)
        have e : ∀ i, (σ (c t) * h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i) *
            (c' t' * g (OrbitPlaces.orbMap D p r' t') a' b' i) =
            (σ (c t) * c' t') * (h (posPl D p (OrbitPlaces.orbMap D p r t) 1) a b i *
              g (OrbitPlaces.orbMap D p r' t') a' b' i) := fun i => by ring
        simp only [e]
        rw [← Finset.mul_sum, hp, if_neg (fun hh => hne hh.1), mul_zero]
      · simp [hc' t' h2]
    · simp [hc t h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hg, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun t' _ => hterm t t'

theorem fOf_isotropic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → (∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf D p σ om R g e' i = 0) ∧ (∀ e e', ∑ i, σ (fOf' D p σ oms R g e i) * fOf' D p σ oms R g e' i = 0) := by
  intro D p _ σ om oms R N N' r g h hO hR hg hp
  constructor
  · intro e e'
    have key := sum_sigma_comb_mul_comb D p σ R g h hO.even hR hg hp e.1.1.2 e'.1.1.2 e.2.1 e'.2.1 e.2.2 e'.2.2
      (fun t => if t.val % 2 = 0 then σ^[t.val] (om e.1.2) else 0)
      (fun t => if t.val % 2 = 0 then σ^[t.val] (om e'.1.2) else 0) 0
      (fun t ht => if_neg ht) (fun t ht => if_neg ht)
    simpa only [fOf, ite_mul, zero_mul] using key
  · intro e e'
    have key := sum_sigma_comb_mul_comb D p σ R g h hO.even hR hg hp e.1.1.2 e'.1.1.2 e.2.1 e'.2.1 e.2.2 e'.2.2
      (fun t => if t.val % 2 = 0 then 0 else σ^[t.val] (oms e.1.2))
      (fun t => if t.val % 2 = 0 then 0 else σ^[t.val] (oms e'.1.2)) 1
      (fun t ht => if_pos (by omega)) (fun t ht => if_pos (by omega))
    simpa only [fOf', ite_mul, zero_mul] using key

end GlobalTheory.KerStd.HypCoord
end
end

