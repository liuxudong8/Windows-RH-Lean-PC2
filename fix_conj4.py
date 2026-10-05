with open(r'C:\proj2\OrderPreservingBijection\InnerProduct.lean', 'r', encoding='utf-8') as f:
    content = f.read()

content = content.replace('integral hyperbolicMeasure3', 'MeasureTheory.integral hyperbolicMeasure3')
content = content.replace('integral hyperbolicMeasure2', 'MeasureTheory.integral hyperbolicMeasure2')

with open(r'C:\proj2\OrderPreservingBijection\InnerProduct.lean', 'w', encoding='utf-8') as f:
    f.write(content)

print('done')
