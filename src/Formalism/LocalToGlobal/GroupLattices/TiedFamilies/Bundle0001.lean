module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0005
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem intSplit_of (I : LocId L p nV W Qq) : Cmp.IntSplit I := fun v t =>
  split_integral_completion F E (I.plc v) (Cmp.splV I v) (fun a => I.spl_alg _ _ a) t

theorem hypAtP_C (I : LocId L p nV W Qq) (hb : Cmp.NotBad I) (hs : Cmp.SelfDualAtP I) : Cmp.HypAtP I :=
  Cmp.isHyperbolicAt_of_integralSplit I hb (intSplit_of I) hs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem natCast_notMem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p n : ℕ} (hp : p.Prime)
    (hv : (p : 𝓞 F) ∈ v.asIdeal) (hn : ¬ p ∣ n) : (n : 𝓞 F) ∉ v.asIdeal := by
  intro hn'
  have hc : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have h1 : ((a * p + b * n : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hn')
  rw [hab, Int.cast_one] at h1
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem notBad_C (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq') : Cmp.NotBad I := by
  unfold Cmp.NotBad
  intro v
  have hv : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ (I.plc v).asIdeal := (I.pl v).2
  unfold GIdx at hg
  obtain ⟨hp, -, -, -, hlev, hT⟩ := hg
  have hne : ∀ i, ¬ D.what₂.places.resChar w ∣ D.host.g i := fun i hd => hlev (by
    rw [(Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime i)).mp hd]
    exact D.host.g_level i)
  exact ⟨natCast_notMem _ hp hv (hne 0), natCast_notMem _ hp hv (hne 1), natCast_notMem _ hp hv hT⟩

theorem isHyperbolicAt_rec_of_isSelfDualAt (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq') (hs : Cmp.SelfDualAtP I) :
    Cmp.HypAtP I :=
  hypAtP_C I (notBad_C D u w hg I) hs

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOne
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {p : ℕ} {G : GAtP p} {A : LocAt F E n G}

def LocInt (A : LocAt F E n G) : Prop :=
  ∀ v (x : G.P.Qq v), x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ A.eQ v x ∈ (A.pl v).1.adicCompletionIntegers F

def LocHyp (S : StepLevel F E σ J T f bad) (A : LocAt F E n G) : Prop :=
  ∀ v (x : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)), x ∈ UPts σ J ((A.pl v).1.adicCompletion F) →
    (∀ a b, (((bc (A.phE v) A.B)⁻¹ * bc (A.ph v) x * bc (A.phE v) A.B : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F) →
    (∀ a b, ((((bc (A.phE v) A.B)⁻¹ * bc (A.ph v) x * bc (A.phE v) A.B)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F) → x ∈ S.Uloc (A.pl v).1

theorem int_of_stab (hW : LocInt A) (v : Fin G.P.nV) (h : GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hh : ∀ a b, (h : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) a b ∈ (algebraMap (G.P.W v) (G.P.Qq v)).range)
    (a b : Fin n) :
    (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) : Matrix (Fin n) (Fin n) _) a b ∈
      (A.pl v).1.adicCompletionIntegers F := by
  have h1 : (bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) h) : Matrix (Fin n) (Fin n) _) a b =
      A.eQ v ((castGL A.rk (G.P.Qq v) h : Matrix (Fin n) (Fin n) _) a b) := rfl
  rw [h1, castGL_apply]
  exact (hW v _).1 (hh _ _)

theorem locHyp_of {k : ℕ} (hk : k = n) (A : LocAt F E n G) (S : StepLevel F E σ J T f bad) (J0 : Matrix (Fin k) (Fin k) E)
    (hJ : ∀ x y, J x y = J0 (Fin.cast hk.symm x) (Fin.cast hk.symm y)) (B0 : GL (Fin k) E) (hB : A.B = reGL hk E B0)
    (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin k) (E ⊗[F] v.adicCompletion F)))
    (hU : ∀ v, S.Uloc v = (Uloc0 v).map (reGL hk _).toMonoidHom)
    (h0 : ∀ v (x : GL (Fin k) (E ⊗[F] (A.pl v).1.adicCompletion F)), x ∈ UPts σ J0 ((A.pl v).1.adicCompletion F) →
      (∀ a b, (((bc (A.phE v) B0)⁻¹ * bc (A.ph v) x * bc (A.phE v) B0 : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a b ∈
        (A.pl v).1.adicCompletionIntegers F) →
      (∀ a b, ((((bc (A.phE v) B0)⁻¹ * bc (A.ph v) x * bc (A.phE v) B0)⁻¹ : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) a b ∈
        (A.pl v).1.adicCompletionIntegers F) → x ∈ Uloc0 (A.pl v).1) : LocHyp S A := by
  subst hk
  obtain rfl : J = J0 := by ext x y; exact hJ x y
  have hre : ∀ (R : Type) [CommRing R] (g : GL (Fin k) R), reGL (rfl : k = k) R g = g := by
    intro R _ g; apply Units.ext; ext x y; rfl
  rw [hre] at hB
  intro v x hx h1 h2
  rw [hB] at h1 h2
  rw [hU]
  exact Subgroup.mem_map.2 ⟨x, h0 v x hx h1 h2, hre _ x⟩

theorem ptOne_of (S : StepLevel F E σ J T f bad) (hW : LocInt A) (hH : LocHyp S A)
    (hbad : ∀ w ∈ bad, ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) : PtOne S G A := by
  intro i L g g' x x' hL hL' hx hx'
  have hoff : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → bc (prV (E := E) w) (x.1⁻¹ * x'.1) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hx.1 w hw, hx'.1 w hw, inv_mul_cancel]
  have hmem : x.1⁻¹ * x'.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) x'.2
  have hU : x.1⁻¹ * x'.1 ∈ S.U := by
    rw [S.U_eq]
    refine ⟨hmem, fun w => ?_⟩
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · obtain ⟨v, rfl⟩ := LocGood.exists_pl A w hw
      have hst : (g v)⁻¹ * g' v ∈ stabStd (k := G.P.m + 1) (Qq := G.P.Qq v) (G.P.W v) := by
        rw [← gMap_std_eq_iff, ← colSpan_eq, ← colSpan_eq, ← hL v, ← hL' v]
      have e : (bc (A.phE v) A.B)⁻¹ * bc (A.ph v) (bc (prV (E := E) (A.pl v).1) (x.1⁻¹ * x'.1)) * bc (A.phE v) A.B =
          bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)) (castGL A.rk (G.P.Qq v) ((g v)⁻¹ * g' v)) := by
        rw [map_mul, map_mul, map_inv, map_inv, hx.2 v, hx'.2 v, map_mul, map_mul, map_inv, map_inv]
        group
      obtain ⟨h1, h2⟩ := (stabStd_iff _ _).1 hst
      refine hH v _ (Formalism.UG.P.afsplit_bc_mem σ J (A.pl v).1 _ hmem) ?_ ?_
      · rw [e]
        exact int_of_stab hW v _ h1
      · rw [e, ← map_inv, ← map_inv]
        exact int_of_stab hW v _ h2
    · rw [hoff w hw]
      exact Subgroup.one_mem _
  refine ⟨⟨_, hU⟩, by group, ?_⟩
  rw [S.chi_triv ⟨_, hU⟩ fun w hw => hoff w (hbad w hw)]
  rfl

end Formalism.L2.G
end
end

