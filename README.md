# Eqratech Arabic Diana Project
# مشروع إقرأتك للعربية - ديانا

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![COQ Proofs](https://img.shields.io/badge/COQ-Verified-green.svg)](arabic-formal-verification/)

مشروع Python لمعالجة اللغة العربية الطبيعية مع جميع أدوات الأفعال والأسماء العربية.

Python NLP Project with all Arabic tools, verbs and names.

---

## 📁 هيكل المشروع | Project Structure

```
Eqratech_Arabic_Diana_Project/
├── 📂 arabic-formal-verification/   # التحقق الرسمي - SFGCOQ
│   ├── coq/                         # ملفات COQ
│   ├── docs/web/                    # واجهة الويب
│   └── install.sh                   # سكربت التثبيت
├── 📂 tests/                        # الاختبارات
├── 📄 *_engine.py                   # محركات المعالجة
├── 📄 *.csv                         # ملفات البيانات
├── 📄 requirements.txt              # المتطلبات
├── 📄 CONTRIBUTING.md               # دليل المساهمة
└── 📄 LICENSE                       # الرخصة
```

---

## 🚀 البدء السريع | Quick Start

### التثبيت | Installation

```bash
# Clone the repository
git clone https://github.com/sonaiso/Eqratech_Arabic_Diana_Project.git
cd Eqratech_Arabic_Diana_Project

# Install Python dependencies
pip install -r requirements.txt
```

### التشغيل | Run

```bash
# تشغيل الخادم
python run_server.py

# أو باستخدام FastAPI مباشرة
uvicorn main:app --reload
```

---

## 📚 المكونات الرئيسية | Main Components

### 1. محركات القواعد النحوية | Grammar Engines

| المحرك | الوصف |
|--------|-------|
| `verbs_engine.py` | محرك الأفعال |
| `phonemes_engine.py` | محرك الفونيمات |
| `gender_engine.py` | محرك الجنس النحوي |
| `demonstratives_engine.py` | محرك أسماء الإشارة |
| `particles_engine.py` | محرك الحروف |

### 2. محركات الصرف | Morphology Engines

| المحرك | الوصف |
|--------|-------|
| `active_participle_engine.py` | اسم الفاعل |
| `passive_participle_engine.py` | اسم المفعول |
| `superlative_engine.py` | أفعل التفضيل |
| `tasgheer_engine.py` | التصغير |

### 3. محركات البلاغة | Rhetoric Engines

| المحرك | الوصف |
|--------|-------|
| `tashbih_engine.py` | التشبيه |
| `istiara_engine.py` | الاستعارة |
| `kinaya_engine.py` | الكناية |
| `tibaq_engine.py` | الطباق |

---

## 🔬 SFGCOQ - التحقق الرسمي | Formal Verification

مشروع فرعي للتحقق الرسمي من القواعد النحوية العربية باستخدام:
- **النحو الوظيفي النظامي (SFG)** - نظرية مايكل هاليداي
- **COQ** - نظام الإثبات الرياضي

### الملفات المُثبتة | Verified Files

```
✓ ArabicGrammar.v      - التعريفات الأساسية
✓ NawasighRules.v      - كان وأخواتها، إنّ وأخواتها
✓ MorphologyRules.v    - قواعد الصرف
```

📖 [التوثيق الكامل](arabic-formal-verification/README.md)

---

## 🧪 الاختبارات | Tests

```bash
# تشغيل الاختبارات
python -m pytest tests/

# التحقق من إثباتات COQ
cd arabic-formal-verification/coq && make verify
```

---

## 🤝 المساهمة | Contributing

نرحب بالمساهمات! راجع [CONTRIBUTING.md](CONTRIBUTING.md) للتفاصيل.

---

## 📄 الرخصة | License

هذا المشروع مرخص تحت [رخصة MIT](LICENSE).

---

## 📞 التواصل | Contact

للأسئلة والاستفسارات، يرجى فتح Issue في المستودع.
