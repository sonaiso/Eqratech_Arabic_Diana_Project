# FractalHub Dictionary

## نظرة عامة (Overview)

القاموس الموحد لمشروع FractalHub - نظام شامل لتمثيل الوحدات اللغوية العربية والبوابات والقواعد الثابتة.

The unified dictionary for the FractalHub project - a comprehensive system for representing Arabic linguistic units, gates, and invariants.

## الإصدارات (Versions)

### الإصدار الثاني (v02) - الحالي

**الملف:** `data/fractalhub_dictionary_v02.yaml`

**المميزات الرئيسية:**
- ✅ بيانات التحكم في الإصدار الصريحة
- ✅ وحدات الصوتيات الذرية (الحركات والتشكيل)
- ✅ وحدات التطريز والتنغيم (Prosody)
- ✅ سجل البوابات المحاذي لطبقات C1/C2/C3/P1/P2/P3
- ✅ تعريفات عمليات الإصلاح والدلتا
- ✅ المستويات المعرفية (اليقين، الظن، الشك)
- ✅ التوافق العكسي الكامل

## البنية (Structure)

```yaml
meta:           # بيانات التحكم في الإصدار
units:          # الوحدات اللغوية (phonemes, morphemes, tokens)
gates:          # البوابات (C1, C2, C3, P1, P2, P3)
evidence:       # الأدلة والمستويات المعرفية
invariants:     # القواعد الثابتة
tags:           # التصنيفات
mappings:       # التوافق العكسي
repair_operations:  # عمليات الإصلاح
unit_delta_ops: # عمليات التحويل
```

## الوحدات (Units)

### أنواع الوحدات:
- **diacritic**: الحركات (َ ُ ِ ْ ّ ً ٌ ٍ)
- **prosody**: علامات الوصل والوقف والتنغيم
- **phoneme**: الأصوات الأساسية (ء ب ت ...)
- **morpheme**: الوحدات الصرفية (ال، ة، ...)
- **token**: الرموز (مسافة، فاصلة، ...)

### مثال:
```yaml
U:DIACRITIC:FATHA:
  unit_id: "U:DIACRITIC:FATHA"
  kind: "diacritic"
  text: "َ"
  features: ["short_vowel", "a_sound", "fatha"]
  status: "active"
```

## البوابات (Gates)

### الطبقات:
- **C1**: التحقق من الترميز (CODEC_VERIFY, DIACRITIC_ATTACH)
- **C2**: القواعد الثابتة (INVARIANTS, MORPHEME_VALIDATE)
- **C3**: المرجع (REFERENCE, SEMANTIC_CHECK)
- **P1**: الصوتيات الأساسية (DOUBLE_SUKUN, ASSIMILATION)
- **P2**: الصوتيات المتقدمة (WASL_BEGIN, STRESS_PATTERN)
- **P3**: التنغيم (PROSODY_ASSIGN, PAUSE_INSERT)

### مثال:
```yaml
G:P1:DOUBLE_SUKUN:
  gate_id: "G:P1:DOUBLE_SUKUN"
  layer: "P1"
  description: "منع السكون المزدوج"
  inputs: ["phoneme_sequence"]
  outputs: ["corrected_sequence"]
  constraints: ["no_consecutive_sukun"]
  evidence_required: true
  penalty: 0.9
  status: "active"
```

## القواعد الثابتة (Invariants)

### أمثلة:
- **INV:NO_ORPHAN_DIACRITIC**: لا يمكن أن تظهر الحركة بدون حرف أساسي
- **INV:DOUBLE_SUKUN_FORBIDDEN**: لا يجوز التقاء ساكنين في النطق
- **INV:TANWIN_FINAL_ONLY**: التنوين يظهر في نهاية الكلمة فقط

## الأدلة والمستويات المعرفية (Evidence Levels)

### المستويات:
- **YAQIN** (1.0): اليقين - تأكيد كامل
- **ZANN** (0.7): الظن - ترجيح قوي
- **SHAKK** (0.4): الشك - احتمال ضعيف

### قواعد الأدلة:
- **NO_MEANING_WITHOUT_EVIDENCE**: لا يمكن إنتاج معنى بدون دليل
- **EVIDENCE_PROPAGATION**: الدليل ينتقل عبر السلسلة

## التحقق من الصحة (Validation)

### استخدام أداة التحقق:
```bash
python scripts/validate_dictionary.py fractalhub/data/fractalhub_dictionary_v02.yaml
```

### ما تتحقق منه الأداة:
- ✅ البنية العامة للملف
- ✅ بيانات التحكم في الإصدار
- ✅ صحة تعريفات الوحدات
- ✅ صحة تعريفات البوابات
- ✅ صحة القواعد الثابتة
- ✅ عدم وجود معرّفات مكررة
- ✅ تنسيق المعرّفات (U:, G:, INV:)

## الاختبارات (Tests)

### تشغيل الاختبارات:
```bash
python -m pytest tests/test_dictionary_load.py -v
```

### ما تختبره:
- ✅ تحميل القاموس بنجاح
- ✅ صحة الإصدار
- ✅ وجود جميع الأقسام المطلوبة
- ✅ بيانات التحكم في الإصدار
- ✅ وحدات الحركات والتطريز
- ✅ البوابات لجميع الطبقات
- ✅ المستويات المعرفية
- ✅ عمليات الإصلاح
- ✅ عدم وجود تكرارات
- ✅ صحة البنية

## الاستخدام (Usage)

### تحميل القاموس في Python:
```python
import yaml
from pathlib import Path

# تحميل القاموس
dict_path = Path("fractalhub/data/fractalhub_dictionary_v02.yaml")
with open(dict_path, 'r', encoding='utf-8') as f:
    dictionary = yaml.safe_load(f)

# الوصول إلى الوحدات
units = dictionary['units']
fatha = units['U:DIACRITIC:FATHA']
print(fatha['text'])  # َ

# الوصول إلى البوابات
gates = dictionary['gates']
sukun_gate = gates['G:P1:DOUBLE_SUKUN']
print(sukun_gate['description'])  # منع السكون المزدوج

# الوصول إلى المستويات المعرفية
evidence = dictionary['evidence']
yaqin = evidence['epistemic_levels']['YAQIN']
print(yaqin['certainty'])  # 1.0
```

## التوافق العكسي (Backward Compatibility)

الإصدار v02 متوافق تمامًا مع v01:
- ✅ `v01_supported: true`
- ✅ `breaking_changes: false`
- ✅ جميع معرّفات v01 محفوظة
- ✅ دعم الإسماء البديلة (aliases)

## التطوير المستقبلي (Future Development)

### الإضافات المخططة:
- [ ] وحدات نحوية إضافية
- [ ] بوابات دلالية (Semantic gates)
- [ ] قواعد ثابتة نحوية متقدمة
- [ ] دعم اللهجات العربية المختلفة
- [ ] واجهة برمجية (API) للوصول إلى القاموس

## المساهمة (Contributing)

عند إضافة وحدات أو بوابات جديدة:
1. اتبع اتفاقيات التسمية (`U:`, `G:`, `INV:`)
2. قم بتضمين جميع الحقول المطلوبة
3. شغّل أداة التحقق للتأكد من الصحة
4. أضف اختبارات للمميزات الجديدة
5. حدّث `changelog` في قسم `meta`

## المراجع (References)

- [YAML Specification](https://yaml.org/spec/)
- [Arabic Unicode Range](https://unicode.org/charts/PDF/U0600.pdf)
- تقييد دفق الطاقة الصوتية (TAQI Framework)

---
آخر تحديث: 2026-01-05
