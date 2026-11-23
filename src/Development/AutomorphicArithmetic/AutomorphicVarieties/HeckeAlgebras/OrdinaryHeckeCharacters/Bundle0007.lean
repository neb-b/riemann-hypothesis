module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.EigChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.MemOrdC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.EqOnTors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  have h1 := s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
  have h2 := s.hA v x
  exact h1.symm.trans h2

private theorem l_notMem {l : ℕ} {L : Type} [Field L] [NumberField L] [IsCMField L] {w u : Plc L}
    (h : ((l : ℕ) : 𝓞 (Lp L)) ∉ (w.under (𝓞 (Lp L))).asIdeal) (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    ((l : ℕ) : 𝓞 L) ∉ u.asIdeal := fun h' => h <| by
  rw [← hu]
  change algebraMap (𝓞 (Lp L)) (𝓞 L) (l : 𝓞 (Lp L)) ∈ u.asIdeal
  rwa [map_natCast]

private theorem cmp_of {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L}
    (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) : cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl

private theorem cmp_loc {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    {x : UA L n} (hx : x ∈ locU n w) (hu : u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) :
    cmp n u ((away l L n).rangeRestrict x) = 1 := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∉ u.asIdeal
  · rw [cmp_of h]
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)
  · unfold CaseU.cmp
    rw [dite_eq_right h]
    rfl

private theorem cLoc_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L} (hw : IsSplitAt w)
    (x : UA L n) (h1 : cLoc w x = 1) (hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) : cLoc u x = 1 := by
  have hw1 : ∀ v, v = w → cLoc v x = 1 := by
    rintro v rfl
    exact h1
  rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
  · exact h1
  · have hce := GlobalTheory.SplitPts.comp_eq x (conjSrc (GlobalTheory.SplitPts.conjE L) w)
    rw [hw1 _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.one_mul] at hce
    exact Units.ext hce

theorem UpperTheory.V.Hi.secU :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ w : Plc L, IsSplitAt w → (∃ j : GLw n w →* UA L n, (∀ g, j g ∈ locU n w) ∧ (∀ g, cLoc w (j g) = g) ∧ Continuous j ∧ ∀ x ∈ locU n w, x = j (cLoc w x)) ∧ (w.under (𝓞 (Lp L)) ∉ s.S → Function.Bijective (((cmp n w).comp (Ub n s).subtype).comp (locA n s w).subtype) ∧ (∀ g, cmp n w ((sec n s w g : Ub n s) : Ga l L n) = g) ∧ ∀ g, sec n s w g ∈ locA n s w) := by
  intro l _ L Ω _ _ _ _ _ _ s n _ w hw
  obtain ⟨e, he⟩ := _root_.GlobalTheory.locU_equiv_GL L n w hw
  have hs : ∀ y, cLoc w (e.symm y : UA L n) = y := fun y => by
    rw [← he, e.apply_symm_apply]
  refine ⟨⟨(locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom, fun g => (e.symm g).2, hs,
    continuous_subtype_val.comp e.symm.continuous, fun x hx => ?_⟩, fun hS => ?_⟩
  · have h1 := he ⟨x, hx⟩
    change x = (e.symm (cLoc w x) : UA L n)
    rw [← h1, e.symm_apply_apply]
  have hl : ((l : ℕ) : 𝓞 (Lp L)) ∉ (w.under (𝓞 (Lp L))).asIdeal := fun h => hS (Or.inl h)
  have hb : Function.Bijective (((cmp n w).comp (Ub n s).subtype).comp (locA n s w).subtype) := by
    refine ⟨(injective_iff_map_eq_one _).2 ?_, fun y => ?_⟩
    · rintro ⟨⟨g, hg⟩, hA⟩ h1
      obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective g
      have h2 : cLoc w x = 1 := (cmp_of (l_notMem hl rfl) x).symm.trans h1
      refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun u => ?_)))
      change cLoc u.1 x = 1
      by_cases hu : u.1.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · exact cLoc_conj hw x h2 hu
      · exact (cmp_of u.2 x).symm.trans
          (MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hA u.1) hu))
    · have hU : (away l L n).rangeRestrict (e.symm y : UA L n) ∈ Ub n s := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun u => ?_, ?_⟩
        · rw [Subgroup.mem_comap, cmp_loc (e.symm y).2 (by
            rw [w_under]
            exact fun h => hS (Or.inr (Or.inl (h ▸ u.2))))]
          exact one_mem _
        · rw [Subgroup.mem_comap, cmp_loc (e.symm y).2 (by
            rw [w_under]
            exact fun h => hS (Or.inr (Or.inr h.symm)))]
          exact one_mem _
      refine ⟨⟨⟨_, hU⟩, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
        MonoidHom.mem_ker.2 (cmp_loc (e.symm y).2 hu)⟩, ?_⟩
      exact (cmp_of (l_notMem hl rfl) _).trans (hs y)
  refine ⟨hb, fun g => ?_, fun g => ?_⟩
  · unfold CaseU.sec
    rw [dite_eq_left hb]
    exact (MulEquiv.ofBijective _ hb).apply_symm_apply g
  · unfold CaseU.sec
    rw [dite_eq_left hb]
    exact ((MulEquiv.ofBijective _ hb).symm g).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreUp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem up_list {σ : Type} [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (g : ∀ v, G v) (w : σ) (s : List σ)
    (hs : s.Nodup) : (s.map fun v => Pi.mulSingle v (g v)).prod w = if w ∈ s then g w else 1 := by
  induction s with
  | nil => simp
  | cons v s ih =>
    rw [List.nodup_cons] at hs
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hs.2]
    by_cases h : w = v
    · subst h; simp [hs.1]
    · simp [h]

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)

private theorem up_VV (d : ℕ) (v v' : H.V) (h : v ≠ v') (g g') (F) :
    H.atV d v g (H.atV d v' g' F) = H.atV d v' g' (H.atV d v g F) := by
  classical
  change (H.X.rpF ℂ d H.m (Pi.mulSingle v g) * H.X.rpF ℂ d H.m (Pi.mulSingle v' g')) F =
    (H.X.rpF ℂ d H.m (Pi.mulSingle v' g') * H.X.rpF ℂ d H.m (Pi.mulSingle v g)) F
  rw [← map_mul, ← map_mul, (Pi.mulSingle_commute (f := fun v : H.V => GLw n (H.Sl v)) h g g').eq]

private theorem up_PA (d : ℕ) (g u) (F) :
    H.X.rpF ℂ d H.m g (H.X.raF d (H.τC ι) u F) = H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m g F) := by
  funext i x k
  change (H.X.ra (H.τC ι) u (fun y j => F j y k) (x * (1, g))) i =
    H.X.ra (H.τC ι) u (fun y j => F j (y * (1, g)) k) x i
  rw [Frame.ra_apply, Frame.ra_apply]
  simp [mul_assoc]

private theorem up_vec (hL : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hH : H.Ax) {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ}
    (Y : H.Part ι lam ξ) (K : H.Lev) (hK : ∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (hω : ∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) (e : ℕ)
    (he : ∀ v i, ∀ y ∈ Uc _ (e + 1), ω v i y = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v)) :
    ∃ F ∈ Y.Y, F ≠ 0 ∧ (∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) ∧
      ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q) := by
  refine Exists.imp (fun F h => ⟨h.1, h.2.1, fun v => h.2.2 (.inl v), fun q => h.2.2 (.inr q)⟩) (Up.meet (I := H.V ⊕ H.Q)
    (Sum.elim (fun v => Set.range (H.atV d v)) fun q => Set.range (H.atW ι d (H.wq q)))
    (Sum.elim (fun v => Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) fun q => fixd (H.atW ι d (H.wq q)) (K.1 q))
    Y.Y Y.ne ?_ ?_ ?_)
  · rintro (v | q) _ ⟨g, rfl⟩
    · exact Up.isoStab (Y.isoL v) g
    · exact Up.isoStab (Y.isoQ q) g
  · rintro (v | q) (v' | q') hne _ ⟨g, rfl⟩
    · exact Up.ordMap _ _ _ (fun g' F => up_VV H d v' v (fun h => hne (by rw [h])) g g' F) _ _ _
    · exact Up.ordMap _ _ _ (fun g' F => (up_PA H ι d _ _ F).symm) _ _ _
    · exact Up.fixMap (H.atW ι d (H.wq q)) (H.atW ι d (H.wq q)) _ (fun g' F => up_PA H ι d _ _ F) _
    · refine Up.fixMap _ _ _ (fun g' F => ?_) _
      change (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F = (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F
      rw [← map_mul, ← map_mul]
      exact congrArg (fun u => H.X.raF d (H.τC ι) u F) (hH.Q_Q q q' (fun h => hne (by rw [h])) g' g).eq.symm
  · rintro (v | q) Z hZ hne hst
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoL v) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2, hu3⟩ := ordA hL _ n _ (Y.σl v).ρ (ω v) (hω v) e (he v) (φ v) (hφ v)
      refine (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, ?_⟩, fun h => hu2 (hp3 (by rw [h, map_zero]))⟩
      exact Up.ordMap _ _ p hp1 _ _ _ u ((Up.mem_ordC _ _ _ _ _).2 ⟨hu1, hu3⟩)
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoQ q) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2⟩ := (Submodule.ne_bot_iff _).1 (hK q)
      exact (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, Up.fixMap _ _ p hp1 _ u hu1⟩,
        fun h => hu2 (hp3 (by rw [h, map_zero]))⟩

private theorem up_ord {A : Type} [CommRing A] (θ : H.X.I.T →* Aˣ) (x : A →+* Qbar l)
    {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} (K : H.Lev)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (e : ℕ)
    (hω : ∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x lam v i u) = 1)
    (hn : ∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v))
    (F : Fin H.m → H.X.Fn ℂ d) (hB : F ∈ H.Big ι ξ) (hV : ∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v)))
    (hQ : ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q)) :
    F ∈ H.OrdAt θ ι x lam ξ K e ∧ ∀ v (j : Fin n),
      H.opC ι lam d (.inr (v, j)) F = ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := by
  classical
  simp only [Up.mem_ordC] at hV
  let I := fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n
  have hN : F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N := Up.fixPi _ (fun v => (I v).N) F fun v => (hV v).1.1
  have hNm : F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) := Up.fixPi _ (fun v => (I v).Nm e) F fun v => (hV v).1.2.1
  have hlev : F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) := by
    intro u hu
    let St : Subgroup H.X.Ub :=
      (MulAction.stabilizer (Module.End ℂ (Fin H.m → H.X.Fn ℂ d))ˣ F).comap (H.X.raF d (H.τC ι)).toHomUnits
    have : H.lev K ≤ St := sup_le (fun u hu => hB.2 u hu) (iSup_le fun q => by
      rintro _ ⟨g, hg, rfl⟩
      exact hQ q g hg)
    exact this hu
  have hCl : F ∈ H.ClAt θ ι x lam ξ K e := by
    refine ⟨⟨⟨⟨hB, hlev⟩, hN⟩, hNm⟩, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro v i y
    have h1 := (hV v).1.2.2 (eT _ n i y)
    rw [hφ v i y, inv_inv, eq_inv_of_mul_eq_one_left (hω v i y)] at h1
    exact h1
  have hz : ∀ v, (I v).uOp (H.atV d v) (I v).z F = ((List.range n).map (psEig (ω v))).prod • F := by
    intro v
    have h1 := (glBridge ((H.Sl v).adicCompletion L) n _ (H.atV d v)).2.2.2.2.2.2.2.2.1
    have h2 := (Up.uOpList (I v) (H.atV d v) F (hV v).1.1 (al _ n) (psEig (ω v)) (List.range n)
      fun j hj => ⟨al_mem _ n j, (hV v).2 j (List.mem_range.1 hj).le⟩).2
    rwa [← h1] at h2
  have hZ := (Up.uOpList (piIwa I) (H.X.rpF ℂ d H.m) F hN (fun v => Pi.mulSingle v (I v).z)
    (fun v => ((List.range n).map (psEig (ω v))).prod) Finset.univ.toList
    fun v _ => ⟨Up.singleP I v _ (I v).z_mem, (Up.uOpPi I _ v _ (I v).z_mem F hN).trans (hz v)⟩).2
  have hzz : (Finset.univ.toList.map fun v => (Pi.mulSingle v (I v).z : GV n H.Sl)).prod = H.X.I.z := by
    funext w
    rw [up_list (fun v => (I v).z) w _ (Finset.nodup_toList _), if_pos (by simp)]
    rfl
  rw [hzz, Finset.prod_map_toList] at hZ
  have hl : ∀ v, ((List.range n).map (psEig (ω v))).prod = ∏ j ∈ Finset.range n, psEig (ω v) j := fun v => rfl
  simp only [hl] at hZ
  refine ⟨?_, fun v j => ?_⟩
  · refine Submodule.mem_iSup_of_mem
      ⟨∏ v, ∏ j ∈ Finset.range n, (H.lowVal ι lam v j)⁻¹ * psEig (ω v) j, ?_⟩ ⟨hCl, ?_⟩
    · rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun j hj => ?_
      rcases j with _ | j
      · simp [HSet.lowVal, psEig]
      · exact hn v ⟨j, by have := Finset.mem_range.1 hj; omega⟩
    · refine Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 ?_)
      change (∏ v, ∏ j ∈ Finset.range n, H.lowVal ι lam v j)⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) H.X.I.z F = _
      rw [hZ, smul_smul]
      simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  · change (H.lowVal ι lam v (j + 1))⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) (Pi.mulSingle v (al _ n (j + 1))) F = _
    rw [Up.uOpPi I _ v _ (al_mem _ n _) F hN, ← smul_smul]
    exact congrArg _ ((hV v).2 _ j.2)

end

theorem UpperTheory.V.Hi.coreUp :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.Part ι lam ξ) (K : H.Lev), (∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥) → ∀ ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) → (∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x.toRingHom lam v i u) = 1) → ∀ a : H.Op → c.O, (∀ w (j : Fin n), ‖ι.symm (Y.a w (j + 1)) - algebraMap c.O (Qbar l) (a (.inl (w, j)))‖ < 1) → (∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1 ∧ ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) - algebraMap c.O (Qbar l) (a (.inr (v, j)))‖ < 1) → ∀ [Fact (CommOn (H.MK θ a K) (H.op A))], H.MK θ a K ≠ ⊥ ∧ ∃ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧ (∀ w (j : Fin n), ι (y (H.gen θ a K (.inl (w, j)))) = Y.a w (j + 1)) ∧ ∀ v (j : Fin n), ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1) := by
  intro hL L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K hK ω hω1 hω2 a ha1 ha2 hFact
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hC, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  choose φ hφ using fun v => Up.exInv (ω v)
  obtain ⟨F, hF, h0, hV, hQ⟩ := up_vec H ι hL hH Y K hK ω hω1 c0 (fun v i y hy => by
    have h := hω2 v i ⟨y, Up.Uc_le _ hy⟩
    rw [hsp.triv v i _ hy, map_one, mul_one] at h
    exact Units.ext h) φ hφ
  obtain ⟨hO, hU⟩ := up_ord H ι θ x.toRingHom K ω c0 hω2 (fun v j => (ha2 v j).1) φ hφ F (Y.le hF) hV hQ
  rw [← hsp.span K c0 le_rfl] at hO
  have hx2 : ∀ b ∈ maximalIdeal A, ‖x.toRingHom b‖ < 1 := Up.normLt x
  have hx1 : ∀ b, ‖x.toRingHom b‖ ≤ 1 := by
    intro b
    obtain ⟨o, ho⟩ := Alg.IsCO.res_surj (O := c.O) b
    have h1 : ‖x (algebraMap c.O A o)‖ ≤ 1 := by
      rw [x.commutes]
      exact (Up.intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) o).map c.O.val)
    have h2 : x.toRingHom b = x.toRingHom (b - algebraMap c.O A o) + x (algebraMap c.O A o) := by simp
    rw [h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx2 _ ho).le h1)
  haveI : Fact (CommOn (locPart (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) fun i => algebraMap c.O A (a i)) (H.op A)) := hFact
  obtain ⟨hne, y, hy1, hy2⟩ := Up.eigPt (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) hC ι x.toRingHom hx1 hx2 sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) F hO h0
    (Sum.elim (fun p => Y.a p.1 (p.2 + 1)) fun p => (H.lowVal ι lam p.1 (p.2 + 1))⁻¹ * psEig (ω p.1) (p.2 + 1))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact Y.sph w _ F hF
      · exact hU v j)
    (fun i => algebraMap c.O A (a i))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact (x.commutes _).symm ▸ ha1 w j
      · exact (x.commutes _).symm ▸ (ha2 v j).2)
  refine ⟨hne, ⟨y, fun o => ?_⟩, RingHom.ext hy1, fun w j => hy2 (.inl (w, j)),
    fun v j => hy2 (.inr (v, j))⟩
  refine Eq.trans (congrArg y ?_) ((hy1 _).trans (x.commutes o))
  exact Subtype.ext (LinearMap.ext fun f => (algebraMap_smul A o f).symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DeformationRingToHeckeAlgebraSurjective
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.deformationRing_to_heckeAlgebra_surjective :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A T B : Type) [CommRing A] [CommRing T] [Algebra c.O T] [Algebra A T] [CommRing B] [Algebra c.O B] (gen : H.Op → T) (D₀ : W.GDet n B H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Bˣ) (f : B →ₐ[c.O] T),
    (∀ (w : H.Wp) (P : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver P w.1 → IsFrob P (normV w.1) σ →
      (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    (∀ v (j : Fin n) (x : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (x : G L Ω) → H.art v x = unif _ →
      ((∏ i with i ≤ j, W.pushCh f.toRingHom (ψ₀ v i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ j : A → B, (∀ b, f (j b) = algebraMap A T b) → Algebra.adjoin A (Set.range gen) = ⊤ → Function.Surjective f := by
  intro L Ω _ _ _ _ _ l _ n c H hH A T B _ _ _ _ _ _ gen D₀ ψ₀ f h1 h2 j hj htop
  have hgen : ∀ i, gen i ∈ f.range := by
    rintro (⟨w, k⟩ | ⟨v, k⟩)
    · obtain ⟨P, hP⟩ := exists_isPlaceOver Ω w.1
      obtain ⟨σ, hσ⟩ := exists_isFrob hP
      have hq : IsUnit ((normV w.1 : ℕ) : c.O) := by
        have h0 := (cycZ L Ω l σ).isUnit.map (algebraMap ℤ_[l] c.O)
        rwa [cycZ_of_isFrob (hH.Wp_away w.1 w.2) hP hσ, map_natCast] at h0
      obtain ⟨u, hu⟩ := hq.exists_left_inv
      have huT : algebraMap c.O T u * ((normV w.1 : ℕ) : T) = 1 := by
        rw [← map_natCast (algebraMap c.O T), ← map_mul, hu, map_one]
      have e := JEx.heckePol_coeff n (normV w.1)
        (fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) (k + 1) k.2
      rw [← h1 w P σ hP hσ, dite_eq_left ⟨Nat.succ_pos _, k.2⟩] at e
      have e2 : (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) =
          (D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).map f.toRingHom := by
        let y := MonoidAlgebra.single (H.prj σ⁻¹) (1 : B)
        have he (z : MonoidAlgebra B H.Gq) : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C
            (MonoidAlgebra.mapRingHom H.Gq f.toRingHom z) =
            MonoidAlgebra.mapRingHom H.Gq (Polynomial.mapRingHom f.toRingHom)
              (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C z) := by
          rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
            ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
            ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
        let : Algebra B T[X] := ((algebraMap T T[X]).comp f.toRingHom).toAlgebra
        have hn := D₀.nat B[X] T[X]
          { toRingHom := Polynomial.mapRingHom f.toRingHom
            commutes' := fun a => by change (Polynomial.mapRingHom f.toRingHom) (C a) = C (f a); simp }
          (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C y)
        change (D₀.map f.toRingHom).D T[X] _ = _
        rw [← show MonoidAlgebra.mapRingHom H.Gq f.toRingHom y =
          MonoidAlgebra.single (H.prj σ⁻¹) 1 by simp [y], he y]
        exact hn
      rw [e2, coeff_map] at e
      have e3 : gen (.inl (w, k)) = algebraMap c.O T u ^ ((k + 1) * (k + 1 - 1) / 2 : ℕ) *
          ((-1) ^ ((k : ℕ) + 1) * f ((D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).coeff (n - (k + 1)))) := by
        refine Eq.trans ?_ (congrArg _ e.symm)
        rw [← mul_assoc, ← mul_pow, huT, one_pow, one_mul]
        rfl
      rw [e3]
      exact mul_mem (pow_mem (f.range.algebraMap_mem u) _)
        (mul_mem (pow_mem (neg_mem (one_mem _)) _) (f.mem_range_self _))
    · obtain ⟨y, hy⟩ := (hH.art_spec v).surj (unif _)
      rw [← h2 v k y (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) y) rfl hy, Units.coe_prod]
      refine prod_mem fun i _ => ?_
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
      exact mul_mem (f.mem_range_self _) (pow_mem (f.range.algebraMap_mem _) _)
  intro t
  have ht : t ∈ Algebra.adjoin A (Set.range gen) := htop ▸ Algebra.mem_top
  change t ∈ f.range
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgen i
  | algebraMap r => exact ⟨j r, hj r⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsOrdinaryCharactersHeckeAlgebra
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.exists_ordinaryCharacters_heckeAlgebra :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : HD Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (φ : Λ.Λ →ₐ[c.O] T) (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ ψ : ∀ v : V.frame.Vl, Fin n → Dec (F := L) (s.A v.1) →* Tˣ, (∀ v i, Alg.AdicCont (maximalIdeal T) fun g => (ψ v i g : T)) →
    (∀ (v : V.frame.Vl) (i : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)) (y : Uo ((s.w v.1).adicCompletion L)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = y →
      (ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) * φ (R.θ (eV n (hset Q R.τ₀).Sl v i y)) = 1) →
    (∀ (v : V.frame.Vl) (j : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
      ((∏ i with i ≤ j, ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ v i, r.IsPsi v i (ψ v i) ∧ W.pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = (ψ v i).comp (V.frame.Iv v).subtype := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hAx T _ _ _ φ gen hgen ψ hc hu hϖ v
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : Finite (ResidueField T) := Finite.of_surjective _ (Alg.resMap_bijective c.O T).2
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hAx.art_spec v
  have hI : ∀ i (g : Dec (F := L) (s.A v.1)) (hg : g ∈ V.frame.Iv v), (ψ v i g : T) = φ (Λ.κ v i ⟨g, hg⟩) := by
    intro i g hg
    have h1 := hu v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl
    have h2 := congrArg (fun z : Λ.Λˣ => φ z) (R.theta v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g hg ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl)
    have h3 : φ ((hset Q R.τ₀).epsV Λ.Λ v g) = (hset Q R.τ₀).epsV T v g := φ.commutes _
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_one, map_one, h3, mul_assoc] at h1 h2
    exact (left_inv_eq_right_inv h1 ((mul_comm _ _).trans h2))
  choose ψ₀ hψ₀ hκ using Λ.inert v
  have hI' : ∀ i (g : Dec (F := L) (s.A v.1)), (g : G L Ω) ∈ Ine (F := L) (s.A v.1) → (ψ v i g : T) = φ (ψ₀ i g) := by
    intro i g hg
    rw [hI i g hg, hκ]
    rfl
  obtain ⟨x, hx⟩ := ha.surj (unif _)
  let p : T →+* ResidueField c.O := Alg.res c.O T
  have hx' : ∀ i, W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) = r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) := by
    intro i
    refine mul_right_cancel (JEx.eq_of_prod
      (fun i : Fin n => W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ))
      (fun i : Fin n => r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ)) (fun j => Units.ext ?_) i)
    have h1 := congrArg p (hϖ v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx)
    have h2 := R.res.unif v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx
    have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inr (v, j)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    have h4 : p ((hset Q R.τ₀).epsV T v (Subgroup.inclusion (Weil_le_Dec _) x)) =
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) := (Alg.res c.O T).commutes _
    refine Eq.trans ?_ ((h1.trans h3).trans h2.symm)
    simp only [Units.coe_prod, map_prod, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    exact Finset.prod_congr rfl fun k _ => congrArg₂ (· * ·) rfl (congrArg (· ^ (k : ℕ)) h4.symm)
  intro i
  refine ⟨⟨hc v i, fun g => ?_, fun g => ?_⟩, MonoidHom.ext fun g => Units.ext (hI i g.1 g.2).symm⟩
  · have h1 : IsLocallyConstant (W.pushCh p (ψ v i)) :=
      IsLocallyConstant.desc _ Units.val (JEx.res_lc (O := c.O) (hc v i)) Units.val_injective
    let β : Dec (F := L) (s.A v.1) →* (ResidueField c.O)ˣ := r.psib v i
    have h2 : IsLocallyConstant β := JEx.lc_of_open _ (r.psib_open v i)
    have h3 := JEx.char_triv (s.hw v.1) ha (W.pushCh p (ψ v i) / β) (h1.div h2) (fun y hy => by
      rw [MonoidHom.div_apply, div_eq_one]
      refine Units.ext ?_
      exact (congrArg p (hI' i y hy)).trans ((Alg.res_map φ _).trans ((hψ₀ i).red y))) x hx (by rw [MonoidHom.div_apply, div_eq_one]; exact hx' i)
    have h4 : W.pushCh p (ψ v i) g / β g = 1 := DFunLike.congr_fun h3 g
    exact congrArg Units.val (div_eq_one.1 h4)
  · obtain ⟨k, hk⟩ := g.2
    have h1 := JEx.eq_on_tors (s.hw v.1) (ψ v i) (W.pushCh (φ : Λ.Λ →+* T) (ψ₀ i)) (hc v i) (JEx.cont_map φ (hψ₀ i).cont)
      (fun y hy => Units.ext (hI' i y hy)) g.1 (l ^ k) (pow_pos (Fact.out : l.Prime).pos k)
      ((QuotientGroup.eq_one_iff _).1 ((map_pow (QuotientGroup.mk' _) _ _).trans hk))
    exact (congrArg Units.val h1).trans ((congrArg φ ((hψ₀ i).mu g)).trans (φ.commutes _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GalResContCoeff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem galResContCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.V.Hi.levelUR2GalRes :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (G : Type) [Group G] [TopologicalSpace G] (n : ℕ) (r : G →* GL (Fin n) (Qbar l)), Continuous r → ∀ φ : G → (ResidueField c.O)[X], IsLocallyConstant φ → ∀ S : Set G, Dense S → (∀ g ∈ S, ∀ (i : ℕ) (b : c.O), residue c.O b = (φ g).coeff i → ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1) → ∀ g (i : ℕ) (b : c.O), residue c.O b = (φ g).coeff i → ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖ < 1 := by
  intro l _ c G _ _ n r hr φ hφ S hS hSb g i b hb
  have hc : Continuous fun h : G => (r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
    (galResContCoeff n i).comp (Units.continuous_val.comp hr)
  have hU : IsOpen {h : G | φ h = φ g} := hφ.isOpen_fiber _
  have hW : IsOpen {h : G | ‖(r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
      (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i‖ < 1} :=
    isOpen_lt (continuous_norm.comp (hc.sub continuous_const)) continuous_const
  obtain ⟨h, ⟨hh1, hh2⟩, hhS⟩ := hS.inter_open_nonempty _ (hU.inter hW) ⟨g, rfl, by simp⟩
  have key := hSb h hhS i b (by rw [hb, Set.mem_setOf_eq.mp hh1])
  have hh2' := Set.mem_setOf_eq.mp hh2
  rw [norm_sub_rev] at hh2'
  calc ‖(r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i - algebraMap c.O (Qbar l) b‖
      = ‖((r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
          (r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i) +
        ((r h : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i -
          algebraMap c.O (Qbar l) b)‖ := by congr 1; abel
    _ ≤ max _ _ := IsUltrametricDist.norm_add_le_max _ _
    _ < 1 := max_lt hh2' key
end

