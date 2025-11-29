# المساهمة في المشروع | Contributing

شكراً لاهتمامك بالمساهمة في مشروع Eqratech Arabic Diana! 🎉

## كيفية المساهمة

### 1. الإبلاغ عن المشاكل (Issues)

- تأكد من أن المشكلة لم يتم الإبلاغ عنها مسبقاً
- استخدم عنواناً واضحاً ووصفاً مفصلاً
- أرفق أمثلة إن أمكن

### 2. إضافة ميزات جديدة (Features)

1. **Fork** المستودع
2. أنشئ فرعاً جديداً:
   ```bash
   git checkout -b feature/اسم-الميزة
   ```
3. أضف تغييراتك مع اختبارات
4. تأكد من اجتياز جميع الاختبارات:
   ```bash
   # للـ Python
   python -m pytest tests/
   
   # للـ COQ
   cd arabic-formal-verification/coq && make verify
   ```
5. **Commit** التغييرات:
   ```bash
   git commit -m "إضافة: وصف الميزة"
   ```
6. **Push** إلى الفرع:
   ```bash
   git push origin feature/اسم-الميزة
   ```
7. افتح **Pull Request**

### 3. معايير الكود

#### Python
- اتبع [PEP 8](https://pep8.org/)
- أضف docstrings للدوال والكلاسات
- استخدم type hints عند الإمكان

#### COQ
- أضف تعليقات للنظريات
- استخدم أسماء وصفية بالعربية والإنجليزية
- أضف أمثلة تطبيقية

### 4. رسائل الـ Commit

استخدم البادئات التالية:
- `إضافة:` لميزة جديدة
- `إصلاح:` لإصلاح خطأ
- `تحسين:` لتحسين الأداء أو الكود
- `توثيق:` لتحديث التوثيق
- `اختبار:` لإضافة اختبارات

مثال:
```
إضافة: قواعد التوكيد في النحو العربي
```

### 5. مراجعة الكود

- ستتم مراجعة PR الخاص بك
- قد يُطلب منك إجراء تعديلات
- بعد الموافقة، سيتم دمج التغييرات

## الموارد المفيدة

- [وثائق COQ](https://coq.inria.fr/documentation)
- [Python Style Guide](https://pep8.org/)
- [النحو الوظيفي النظامي](https://en.wikipedia.org/wiki/Systemic_functional_grammar)

## قواعد السلوك

- كن محترماً ومهذباً
- رحب بالمساهمين الجدد
- ركز على التحسين البنّاء

---

# Contributing (English)

Thank you for your interest in contributing to Eqratech Arabic Diana Project! 🎉

## How to Contribute

### Reporting Issues
- Check if the issue already exists
- Use a clear title and detailed description
- Include examples when possible

### Adding Features
1. Fork the repository
2. Create a feature branch: `git checkout -b feature/feature-name`
3. Add your changes with tests
4. Ensure all tests pass
5. Commit with descriptive message
6. Push and create a Pull Request

### Code Standards
- **Python**: Follow PEP 8, add docstrings and type hints
- **COQ**: Add comments, use descriptive names, include examples

## Resources
- [COQ Documentation](https://coq.inria.fr/documentation)
- [Python PEP 8](https://pep8.org/)
