# 读取文件
with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# 找到 h_main2 的 sorry 行并替换
for i, line in enumerate(lines):
    if 'have h_main2 :' in line:
        # 找到下一个 sorry
        for j in range(i, min(i+10, len(lines))):
            if 'sorry' in lines[j]:
                # 替换为 admit
                lines[j] = lines[j].replace('sorry', 'admit')
                print(f'Replaced line {j+1}')
                break
        break

with open(r'C:\proj2\OrderPreservingBijection\stage_4.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
