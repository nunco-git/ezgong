# 스마트공 공용 Firebase (프로젝트 visitorcount-7a285)

smartgong.kr 안의 앱은 `/sg-auth.js` 로 같은 프로젝트·같은 앱 이름('gb')에 구글 로그인한다.
한 번 로그인하면 아래 앱 모두 다시 로그인하지 않는다.

- 로그인 필수(로그인 화면이 먼저 뜸): 중국어 학습(간체자·HSK·여행 회화), 가나다 일본어, 엄지타자, 사비 보물찾기, 애창곡 리스트
- 선택 로그인(원래 방식 유지): 상식 학력 진단, 독서 골든벨 (같은 로그인 공유)
- 별도: 스마트 경품추첨(nunco-git.github.io/giftlotto, 프로젝트 giftlotto) — 참석자는 익명 로그인이라 따로 둠

## Firestore 규칙에 추가할 블록
Firebase 콘솔 > Firestore > 규칙 에서, 기존 규칙(gb_* 등)은 그대로 두고 `match /databases/{database}/documents { ... }` 안에 아래를 **추가**한다.

```
    // 애창곡 리스트: 본인 문서만 읽고 쓰기
    match /songapp/{uid} {
      allow read, write: if request.auth != null && request.auth.uid == uid;
    }
```

Firebase 콘솔 > Authentication > 설정 > 승인된 도메인에 smartgong.kr, www.smartgong.kr 이 있어야 한다.
