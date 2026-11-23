module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0004
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0013

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.AlgebraMapIntIntAf
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section TL

variable {F : Type} [Field F] [NumberField F]

theorem algebraMap_int_intAf (t : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F t) ∈ intAf F := by
  intro w
  show (algebraMap F (Af F) (algebraMap (𝓞 F) F t)) w ∈ w.adicCompletionIntegers F
  rw [af_alg_apply, HeightOneSpectrum.mem_adicCompletionIntegers]
  have e1 : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F t) =
      ((algebraMap (𝓞 F) F t : F) : w.adicCompletion F) := rfl
  rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one w t

theorem finElt (m : 𝓞 F) (hm : m ≠ 0) : {w : HeightOneSpectrum (𝓞 F) | m ∈ w.asIdeal}.Finite := by
  have hI : Ideal.span {m} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hm
  apply (Ideal.finite_factors hI).subset
  intro w hw
  show w.asIdeal ∣ Ideal.span {m}
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hw

theorem evT_compl (X : Set (HeightOneSpectrum (𝓞 F))) : 1 - evT Xᶜ = evT X := by
  apply af_ext
  intro u
  rw [af_sub_apply, af_one_apply, evT_apply, evT_apply]
  by_cases h : u ∈ X
  · rw [if_neg (fun h' => h' h), if_pos h, sub_zero]
  · rw [if_pos (show u ∈ Xᶜ from h), if_neg h, sub_self]

theorem evT_inv_int (X : Set (HeightOneSpectrum (𝓞 F))) (t : 𝓞 F) (ht : ∀ u ∈ X, t ∉ u.asIdeal) :
    evT X * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹) ∈ intAf F := by
  rw [← evT_compl]
  exact one_sub_evT_inv_int Xᶜ t (fun u hu => ht u (by simpa using hu))

theorem evT_mul_of_subset {X Y : Set (HeightOneSpectrum (𝓞 F))} (hXY : X ⊆ Y) : evT X * evT Y = evT X := by
  apply af_ext
  intro u
  rw [af_mul_apply, evT_apply, evT_apply]
  by_cases h : u ∈ X
  · rw [if_pos h, if_pos (hXY h), mul_one]
  · rw [if_neg h, zero_mul]

theorem evT_split {B S : Set (HeightOneSpectrum (𝓞 F))} (hBS : B ⊆ S) : evT S = evT B + evT (S \ B) := by
  apply af_ext
  intro u
  rw [af_add_apply, evT_apply, evT_apply, evT_apply]
  by_cases h1 : u ∈ B
  · rw [if_pos (hBS h1), if_pos h1, if_neg (fun h => h.2 h1), add_zero]
  · by_cases h2 : u ∈ S
    · rw [if_pos h2, if_neg h1, if_pos ⟨h2, h1⟩, zero_add]
    · rw [if_neg h2, if_neg h1, if_neg (fun h => h2 h.1), add_zero]

theorem t_lemma (v : HeightOneSpectrum (𝓞 F)) (m : 𝓞 F) (hm : m ≠ 0) :
    ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      (1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m) ∈ intAf F := by
  classical
  have hn : ∀ w : HeightOneSpectrum (𝓞 F), ∃ n : ℕ, m ∉ w.asIdeal ^ n := by
    intro w
    by_contra h
    push_neg at h
    have hmem : m ∈ ⨅ i, w.asIdeal ^ i := (Submodule.mem_iInf _).2 h
    rw [Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top, Ideal.mem_bot] at hmem
    exact hm hmem
  choose n hn using hn
  let s : Finset (HeightOneSpectrum (𝓞 F)) := insert v (finElt m hm).toFinset
  obtain ⟨t, ht⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s) (fun w => w.asIdeal)
    (fun w => if w = v then 1 else n w) (fun w _ => w.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if (w : HeightOneSpectrum (𝓞 F)) = v then 1 else 0)
  refine ⟨t, ?_, ?_⟩
  · intro htv
    have h1 : t - 1 ∈ v.asIdeal := by simpa using ht v (Finset.mem_insert_self _ _)
    have h2 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have := v.asIdeal.sub_mem htv h1
      simpa using this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · intro w
    show ((1 - evT {v}) * algebraMap F (Af F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m)) w ∈
      w.adicCompletionIntegers F
    rw [af_mul_apply, af_sub_apply, evT_apply, af_one_apply, af_alg_apply]
    split_ifs with hw
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers]
      have e1 : algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m) =
          ((algebraMap (𝓞 F) F t / algebraMap (𝓞 F) F m : F) : w.adicCompletion F) := rfl
      rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_div₀,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
      have hw' : w ≠ v := fun h => hw (by rw [h]; exact Set.mem_singleton v)
      have hpos : 0 < w.intValuation m := zero_lt_iff.2 (HeightOneSpectrum.intValuation_ne_zero w m hm)
      by_cases hmw : m ∈ w.asIdeal
      · have hws : w ∈ s := Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hmw)
        have h1 := ht w hws
        simp only [if_neg hw', sub_zero] at h1
        have hle := (HeightOneSpectrum.intValuation_le_pow_iff_mem w t (n w)).2 h1
        have hnot : ¬ w.intValuation m ≤ WithZero.exp (-((n w : ℕ) : ℤ)) :=
          fun h => hn w ((HeightOneSpectrum.intValuation_le_pow_iff_mem w m (n w)).1 h)
        have hlt := lt_of_le_of_lt hle (not_le.1 hnot)
        exact (div_le_one₀ hpos).2 hlt.le
      · rw [(HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w m).2 hmw, div_one]
        exact HeightOneSpectrum.intValuation_le_one w t

end TL

section FL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ}

theorem tmul_one_smul_Fsmul (a : Af F) (c : F) (Y : Fin M → Af F ⊗[F] E) :
    (a ⊗ₜ[F] (1 : E)) • (c • Y) = ((a * algebraMap F (Af F) c) ⊗ₜ[F] (1 : E)) • Y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_smul_comm, show a * algebraMap F (Af F) c = c • a by rw [Algebra.smul_def, mul_comm],
    ← TensorProduct.smul_tmul', smul_mul_assoc]

theorem tmul_one_smul_smul (a a' : Af F) (Y : Fin M → Af F ⊗[F] E) :
    (a ⊗ₜ[F] (1 : E)) • ((a' ⊗ₜ[F] (1 : E)) • Y) = ((a * a') ⊗ₜ[F] (1 : E)) • Y := by
  rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem crd_iff (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (s : 𝓞 F) (w : V) :
    algebraMap (𝓞 F) (𝓞 E) s • w ∈ L0 ↔ (algebraMap (𝓞 F) F s) • b.equivFun w ∈ crdOf b L0 := by
  rw [mem_iff_crdOf b L0, equivFun_osmul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 F) F E, algebraMap_smul]

end FL

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermSk
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def Sw (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : HeightOneSpectrum (𝓞 F)) : Submonoid (𝓞 E) :=
  t.asIdeal.primeCompl.map (algebraMap (𝓞 F) (𝓞 E))

def LocSw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E), (∀ a, σ a = star a) → (∀ e, σ e = e → ∃ c : F, algebraMap F E c = e) →
    ∀ (V : Type) [AddCommGroup V] [Module (𝓞 E) V] (p : Ideal (𝓞 E)), p.IsMaximal →
    ∀ t : HeightOneSpectrum (𝓞 F), t.asIdeal = p.comap (algebraMap (𝓞 F) (𝓞 E)) →
    ∀ X : Submodule (𝓞 E) V, loc (K := E) p X = locS (Sw F E t) X

def CloseLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ e, σ (σ e) = e) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det → Submodule.IsFullLattice E L0 →
    ∀ g : GL (Fin M) E, g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ D' : 𝓞 F, D ∣ D' → ∀ γ : GL (Fin M) E, γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
      ∀ t : HeightOneSpectrum (𝓞 F),
      (∀ i j, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E)
          (t.adicCompletionIntegers F).toSubring,
        PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) ((g : Matrix (Fin M) (Fin M) E) i j) -
            PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) ((γ : Matrix (Fin M) (Fin M) E) i j) =
          PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (D' : F)) * s) →
      locS (Sw F E t) (gmap (linOf b γ) L0) = locS (Sw F E t) (gmap (linOf b g) L0)

def WPlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : Ideal (𝓞 E)), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥

def BcU : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E),
    g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    Units.map ((PI.UnitaryApproxDefs.inclE (F := F) (E := E) R).mapMatrix :
      Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[F] R)).toMonoidHom g ∈ PI.UnitaryApproxDefs.UPts σ J R

def GramOK : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [StarRing E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ a, σ a = star a) → ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V),
    h.IsSymm → h.Nondegenerate → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) (gramOf h b) ∧ IsUnit (gramOf h b).det

abbrev Fix {E : Type} [Field E] (s : E →+* E) : Subfield E := RingHom.eqLocusField s (RingHom.id E)

def sigFix {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) :
    E →ₐ[Fix (σ : E →+* E)] E :=
  { (σ : E →+* E) with commutes' := fun r => r.2 }

theorem hermApprox_of (hL : LocSw) (hC : CloseLoc) (hW : WPlace) (hB : BcU) (hG : GramOK) :
    HermApprox := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hS hN hL0 N hNg P hP
  classical
  have hσσ : ∀ e, σ (σ e) = e := fun e => by rw [hσ, hσ, star_star]
  obtain ⟨hH, hdet⟩ := hG F E σ hσ V h M b hS hN
  set J := gramOf h b with hJ
  let K0 : Subfield E := Fix (σ : E →+* E)
  let σ0 : E →ₐ[K0] E := sigFix σ
  have hσ0 : ∀ e, σ0 e = σ e := fun _ => rfl
  have hσσ0 : ∀ e, σ0 (σ0 e) = e := fun e => hσσ e
  have hθ0 : ∃ θ, σ0 θ ≠ θ := hθ
  have hH0 : PI.UnitaryApproxDefs.IsHerm (σ0 : E →+* E) J := hH
  have hfix : ∀ e, σ0 e = e → ∃ c : K0, algebraMap K0 E c = e := fun e he => ⟨⟨e, he⟩, rfl⟩
  have hσstar : ∀ a, σ0 a = star a := fun a => hσ a

  have wit : ∀ p : P, ∃ u ∈ isom h,
      gmap u (loc (K := E) (p : Ideal (𝓞 E)) L0) = loc (K := E) (p : Ideal (𝓞 E)) N :=
    fun p => hNg.2 p (hP p p.2)
  choose u hu hul using wit
  let g : P → GL (Fin M) E := fun p => matGL b (u p)
  have hg : ∀ p, g p ∈ PI.UnitaryApproxDefs.UJ (σ0 : E →+* E) J := fun p => matGL_mem σ hσ h b (hu p)

  let w : P → HeightOneSpectrum (𝓞 K0) := fun p =>
    ⟨(p : Ideal (𝓞 E)).comap (algebraMap (𝓞 K0) (𝓞 E)),
      by have := (hP _ p.2).isPrime; infer_instance, hW K0 E _ (hP _ p.2)⟩
  let T : Finset (HeightOneSpectrum (𝓞 K0)) := Finset.univ.image w
  let gl : (t : HeightOneSpectrum (𝓞 K0)) → GL (Fin M) (E ⊗[K0] t.adicCompletion K0) := fun t =>
    if hx : ∃ p, w p = t then
      Units.map ((PI.UnitaryApproxDefs.inclE (F := K0) (E := E) (t.adicCompletion K0)).mapMatrix :
        Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[K0] t.adicCompletion K0)).toMonoidHom
          (g (Classical.choose hx))
    else 1
  have hgl : ∀ t ∈ T, gl t ∈ PI.UnitaryApproxDefs.UPts σ0 J (t.adicCompletion K0) := by
    intro t _
    by_cases hx : ∃ p, w p = t
    · simp only [gl, dif_pos hx]
      exact hB K0 E σ0 M J _ _ (hg _)
    · simp only [gl, dif_neg hx]
      exact one_mem _

  have hCp := fun p : P => hC K0 E σ0 V M J b L0 hσσ0 hH0 hdet hL0 (g p) (hg p)
  choose D hD0 hDcl using hCp
  let Dall : 𝓞 K0 := ∏ p, D p
  have hDall : Dall ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hD0 p
  obtain ⟨γ, hγ, hc⟩ := unitary_approximation_finite K0 E (Fin M) σ0 J hσσ0 hθ0 hH0 hdet
    T gl hgl Dall hDall
  refine ⟨⟨γ, hγ⟩, fun q hq => ?_⟩
  let q' : P := ⟨q, hq⟩
  have hx : ∃ p, w p = w q' := ⟨q', rfl⟩
  set ps := Classical.choose hx with hps
  have hpw : w ps = w q' := Classical.choose_spec hx
  have hT : w q' ∈ T := Finset.mem_image_of_mem w (Finset.mem_univ _)
  have hcong := hc (w q') hT
  have hglq : gl (w q') = Units.map ((PI.UnitaryApproxDefs.inclE (F := K0) (E := E) ((w q').adicCompletion K0)).mapMatrix :
        Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[K0] (w q').adicCompletion K0)).toMonoidHom
          (g ps) := dif_pos hx
  rw [hglq] at hcong
  have hcl := hDcl ps Dall (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) γ hγ (w q') hcong
  have eq1 := hL K0 E σ0 hσstar hfix V q (hP q hq) (w q') rfl
  have eq2 := hL K0 E σ0 hσstar hfix V (ps : Ideal (𝓞 E)) (hP _ ps.2) (w q') (by rw [← hpw])
  show loc (K := E) q (gmap (linOf b γ) L0) = loc (K := E) q N
  rw [eq1, eq1, hcl, ← eq2, ← eq2, linOf_matGL, locGmapStep E V (u ps) (ps : Ideal (𝓞 E)) L0]
  exact hul ps

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PsiInclR
section
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Apx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem Psi_sigR (v : HeightOneSpectrum (𝓞 F)) (x : Af F ⊗[F] E) :
    Psi v (PI.UJClassFin.sigR (Af F) σ x) = PI.UnitaryApproxDefs.sigR σ (Fv F v) (Psi v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have e1 : PI.UJClassFin.sigR (Af F) σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [PI.UJClassFin.sigR]
    rw [e1, Psi_tmul, Psi_tmul]
    simp [PI.UnitaryApproxDefs.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Psi_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    Psi v (inclR (F := F) (Af F) e) = PI.UnitaryApproxDefs.inclE (F := F) (Fv F v) e := by
  show Psi v ((1 : Af F) ⊗ₜ[F] e) = e ⊗ₜ[F] (1 : Fv F v)
  rw [Psi_tmul]; rfl

def finU (g : HA (AF F) σ J) : GL (Fin M) (Af F ⊗[F] E) :=
  ⟨finMat σ J g, finMat σ J g⁻¹, by rw [← finMat_mul, mul_inv_cancel, finMat_one],
    by rw [← finMat_mul, inv_mul_cancel, finMat_one]⟩

def gLoc (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) : GL (Fin M) (E ⊗[F] Fv F v) :=
  Units.map ((Psi (E := E) v).toRingHom.mapMatrix : Matrix (Fin M) (Fin M) (Af F ⊗[F] E) →+*
    Matrix (Fin M) (Fin M) (E ⊗[F] Fv F v)).toMonoidHom (finU σ J g)

theorem gLoc_val (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) (E ⊗[F] Fv F v)) =
      (finMat σ J g).map (Psi v) := rfl

theorem gLoc_mem (g : HA (AF F) σ J) (v : HeightOneSpectrum (𝓞 F)) :
    gLoc σ J g v ∈ PI.UnitaryApproxDefs.UPts σ J (Fv F v) := by
  show PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (Fv F v)) ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) _) *
      J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v)) * ((gLoc σ J g v : GL (Fin M) (E ⊗[F] Fv F v)) : Matrix (Fin M) (Fin M) _) =
    J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v))
  rw [gLoc_val]
  have hU := congrArg (fun X => X.map (Psi (E := E) v)) (finMat_unitary σ J g)
  beta_reduce at hU
  rw [mapAlg_mul, mapAlg_mul] at hU
  have hcT : ∀ X : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (PI.UJClassFin.cT (PI.UJClassFin.sigR (Af F) σ) X).map (Psi v) = PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ (Fv F v)) (X.map (Psi v)) := by
    intro X; ext i j; simp [PI.UJClassFin.cT, PI.UnitaryApproxDefs.cT, Psi_sigR]
  have hJ : (JR (Af F) J).map (Psi (E := E) v) = J.map (PI.UnitaryApproxDefs.inclE (F := F) (Fv F v)) := by
    ext i j; simp [JR, Psi_inclR]
  rw [hcT, hJ] at hU
  exact hU

theorem approxT (hσσ : ∀ e, σ (σ e) = e) (hθ : ∃ θ, σ θ ≠ θ) (hH : PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J)
    (hdet : IsUnit J.det) (g : HA (AF F) σ J) (T : Finset (HeightOneSpectrum (𝓞 F))) (N0 : ℕ)
    (hN0 : 0 < N0) :
    ∃ γ : PI.UJClassFin.UJ (σ : E →+* E) J, ∀ i j, ∃ o ∈ Oh F E,
      (evT (T : Set (HeightOneSpectrum (𝓞 F))) ⊗ₜ[F] (1 : E)) *
        (finMat σ J g i j - inclR (F := F) (Af F) (((γ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j)) =
        N0 • o := by
  classical
  have hD : ((N0 : 𝓞 F)) ≠ 0 := by exact_mod_cast hN0.ne'
  obtain ⟨γ, hγ, hc⟩ := unitary_approximation_finite F E (Fin M) σ J hσσ hθ hH hdet T
    (fun w => gLoc σ J g w) (fun w _ => gLoc_mem σ J g w) (N0 : 𝓞 F) hD
  refine ⟨⟨γ, hγ⟩, fun i j => ?_⟩
  show ∃ o ∈ Oh F E, (evT (T : Set (HeightOneSpectrum (𝓞 F))) ⊗ₜ[F] (1 : E)) *
        (finMat σ J g i j - inclR (F := F) (Af F) ((γ : Matrix (Fin M) (Fin M) E) i j)) = N0 • o
  have hc' : ∀ w : T, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (Fv F w.1) (PI.UnitaryApproxDefs.intOE E) (w.1.adicCompletionIntegers F).toSubring,
      Psi w.1 (finMat σ J g i j) - PI.UnitaryApproxDefs.inclE (F := F) (Fv F w.1) ((γ : Matrix (Fin M) (Fin M) E) i j) =
        PI.UnitaryApproxDefs.inclE (F := F) (Fv F w.1) (algebraMap F E ((N0 : 𝓞 F) : F)) * s := fun w => hc w.1 w.2 i j
  choose s hs hse using hc'
  refine ⟨∑ w : T, (sgl w.1 1 ⊗ₜ[F] (1 : E)) * Phi w.1 (s w),
    AddSubgroup.sum_mem _ fun w _ => Oh_mul (tmul_mem_Oh (sgl_int _ (one_mem _)) isIntegral_one) (Phi_int _ (hs w)), ?_⟩
  rw [evT_eq_sum, TensorProduct.sum_tmul, Finset.sum_mul, ← Finset.sum_coe_sort T, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Phi_Psi, map_sub, Psi_inclR, hse w, Phi_mul, Phi_inclE]
  have e0 : ((N0 : 𝓞 F) : F) = (N0 : F) := by simp
  have e1 : sgl w.1 1 ⊗ₜ[F] (algebraMap F E ((N0 : 𝓞 F) : F)) = N0 • (sgl w.1 1 ⊗ₜ[F] (1 : E)) := by
    rw [e0, show algebraMap F E (N0 : F) = (N0 : F) • (1 : E) by rw [Algebra.smul_def, mul_one],
      TensorProduct.tmul_smul, Nat.cast_smul_eq_nsmul]
  rw [e1, smul_mul_assoc]

end Apx

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

