# Lời thuyết trình cho `reportII.pptx`

**Từ kiểm chứng có AI hỗ trợ đến phát hiện lỗi bảo mật**
Seminar 45 phút · Hoàng Lê Trường · Thứ Sáu, 16/10/2026

Mỗi mục dưới đây tương ứng với một slide. Phần in nghiêng ở đầu là thời lượng gợi ý; phần văn bản là lời nói gợi ý, có thể đọc gần như nguyên văn. Toàn bộ nội dung này cũng được nhúng vào speaker notes của file `.pptx`.

---

## Slide 1 — Trang bìa

*Thời lượng: 1 phút.*

Xin chào mọi người. Tôi muốn mở đầu bằng một câu hỏi rất đơn giản: **nếu một AI nói với chúng ta rằng một chương trình là đúng, chúng ta có nên tin không?**

Hôm nay tôi sẽ kể lại một dự án cụ thể: chúng tôi dùng AI để hỗ trợ kiểm chứng hình thức một thành phần mật mã của Signal — Sparse Post-Quantum Ratchet, gọi tắt là SPQR — bằng Lean 4. Kết quả là 246 file đặc tả được chứng minh hoàn chỉnh, và đồng thời phát hiện 63 lỗi, trong đó có những lỗi mà bản thân các chứng minh không hề nhắc đến.

Bài nói nằm ở giao điểm của ba lĩnh vực: trí tuệ nhân tạo, kiểm chứng hình thức, và bảo mật phần mềm. Người nghe không cần biết trước Lean hay mật mã học; mục tiêu là hiểu cách tiếp cận và ý nghĩa thực tiễn của nó.

## Slide 2 — Lộ trình

*Thời lượng: 1 phút.*

Bài nói gồm năm phần. Phần 1 đặt vấn đề: vì sao phần mềm vượt qua mọi bài test vẫn có thể sai. Phần 2 giới thiệu kiểm chứng hình thức và Lean. Phần 3 nói về cách AI hỗ trợ kiểm chứng và những điểm cần cảnh giác. Phần 4 là trọng tâm — case study SPQR với 63 lỗi, trong đó tôi đi sâu vào một lỗi gây deadlock vĩnh viễn, lỗi D21. Phần 5 là bài học và thảo luận.

Một điểm khác với cách trình bày thông thường: sau mỗi slide khái niệm, tôi sẽ chèn ngay một slide bằng chứng từ dự án thật, để lý thuyết luôn được minh họa bằng dữ liệu cụ thể.

---

## Slide 3 — Chúng ta có thể tin phần mềm không?

*Phần 1 · 5 phút (cùng slide 4).*

Một chương trình có thể vượt qua mọi bài test mà chúng ta nghĩ ra — và vẫn chứa lỗi.

Hãy nhìn đoạn mã bên phải: kiểm tra quyền, rồi mới thực hiện thao tác. Trông hoàn toàn hợp lý. Nhưng câu hỏi là: kiểm tra điều kiện này có đủ để bảo đảm thao tác an toàn không? Trong thực tế, vấn đề thường không nằm ở câu `if`, mà nằm ở chỗ **trạng thái đã bị thay đổi trước khi điều kiện được kiểm tra**, hoặc kẻ tấn công cố tình tìm một chuỗi thao tác bất thường mà người viết test không nghĩ đến.

Ba khái niệm nên phân biệt: *bug* là chương trình không chạy như mong đợi; *security defect* là lỗi ảnh hưởng đến tính bảo mật, chẳng hạn quyền truy cập hay tính toàn vẹn trạng thái; *vulnerability* là điểm yếu có thể bị khai thác trong điều kiện cụ thể. Không phải mọi bug đều là vulnerability — và chúng ta sẽ thấy điều đó rất rõ ở slide 17.

Thông điệp ở thanh dưới: testing tìm lỗi trong những lần chạy được chọn; kiểm chứng hình thức lập luận về tính chất của chương trình với *mọi* đầu vào.

## Slide 4 — Một lỗi thật: D1

*Phần 1 · bằng chứng.*

Đây là lỗi đầu tiên trong danh sách 63 lỗi, để mọi người thấy vấn đề không phải lý thuyết.

SPQR lưu trạng thái phiên dưới dạng một blob protobuf. Khi đọc blob đó lên, hàm `from_pb` sao chép các trường vào cấu trúc trong bộ nhớ. Hình vẽ cho thấy: từ blob đến câu lệnh `assert` kiểm tra `next.len()`, không có bất kỳ bước nào kiểm tra lại độ dài. Hợp đồng do hax ghi lại chỉ được kiểm chứng ở *thời điểm chứng minh*, không tồn tại ở thời điểm chạy. Kết quả là một blob bị hỏng — do lỗi ổ đĩa, do đồng bộ sai, hay do cố ý — làm chương trình panic.

Lưu ý: Signal có test, và Signal có chứng minh hax/F*. Cả hai đều "xanh". Lỗi này nằm ngoài vùng mà cả hai cùng nhìn.

---

## Slide 5 — Testing và kiểm chứng hình thức

*Phần 2 · 8 phút (cùng slide 6–8).*

Bên trái là testing. Nó chạy chương trình trên những đầu vào được chọn, và chỉ chứng minh được *sự tồn tại* của lỗi, không chứng minh được *sự vắng mặt* của lỗi. Trong SPQR, chúng tôi bắn 40.000 thông điệp giả mạo vào hàm nhận — không có panic nào. Và testing bỏ sót toàn bộ nhóm lỗi đi qua đường blob như D1, D19, D23.

Bên phải là kiểm chứng hình thức. Ta phát biểu một tính chất cho mọi đầu vào và chứng minh nó trong một mô hình. SPQR có 246 file đặc tả Lean, không có `sorry` nào. Điều quan trọng nhất: **mỗi định lý phải nêu rõ giả thiết của nó**. Và đây là ý tưởng then chốt của toàn bộ dự án — nếu một định lý cần giả thiết X, mà mã Rust không bao giờ kiểm tra X, thì khoảng cách đó chính là một lỗi.

Ví dụ cộng hai số ở dưới được chọn vì chưa cần đến mật mã học: test chỉ thử vài cặp số; chứng minh bao phủ mọi cặp — *với điều kiện* bài toán được hình thức hóa đúng. Cụm "với điều kiện" đó là chủ đề của slide tiếp theo.

## Slide 6 — Đặc tả, hiện thực, chứng minh

*Thời lượng: 3 phút.*

Đây là một trong những slide quan trọng nhất của bài nói.

Ba câu hỏi: hệ thống *nên* làm gì (đặc tả); mã *thực sự* làm gì (hiện thực); và *vì sao* hiện thực thỏa mãn đặc tả (chứng minh). Ví dụ về đặc tả: "một thông điệp chưa xác thực không được làm trạng thái phiên tiến lên". Hãy nhớ câu này — toàn bộ phần 4 xoay quanh nó.

Câu hỏi màu đỏ: **điều gì xảy ra nếu bản thân đặc tả sai hoặc thiếu?** Nếu đặc tả chỉ nói hàm trả về đúng với đầu vào hợp lệ, mà không nói gì về đầu vào không hợp lệ, thì chứng minh có thể hoàn toàn đúng về mặt toán học mà vẫn bỏ qua đúng trường hợp kẻ tấn công quan tâm.

## Slide 7 — Lean là gì?

*Thời lượng: 2 phút.*

Lean là một trợ lý chứng minh tương tác, đồng thời là một ngôn ngữ lập trình. Nó cho phép phát biểu định nghĩa và định lý chính xác, xây dựng chứng minh bằng tactic, và — quan trọng nhất — mọi chứng minh đều được kiểm tra lại bởi một nhân (kernel) nhỏ, đáng tin cậy.

Ví dụ bên phải rất nhỏ: `n + 0 = n`, chứng minh bằng `rfl`, tức là hai vế bằng nhau theo định nghĩa. Không cần hiểu sâu cú pháp. Điều cần nhớ nằm ở thanh dưới: **Lean kiểm tra xem chứng minh có thiết lập đúng mệnh đề đã khai báo hay không — và chỉ thế thôi.** Lean không kiểm tra mệnh đề đó có phải là yêu cầu bảo mật đúng hay không.

## Slide 8 — Pipeline kiểm chứng SPQR

*Phần 2 · bằng chứng.*

Đây là cách chúng tôi đưa mã Rust vào Lean. Công cụ Aeneas dịch mã Rust thành các định nghĩa Lean trong file `Funs.lean`; file này được sinh tự động và được tin cậy. Chúng tôi viết đặc tả và chứng minh trên các định nghĩa đó.

Phần vẽ nét đứt là các *mô hình ngoài* viết tay — mô hình của ML-KEM, HMAC, và các thư viện mà Aeneas không dịch được. Đây là điểm yếu của mọi pipeline kiểu này: nếu một mô hình viết tay không đúng với thư viện thật, mọi chứng minh dựa vào nó bị suy yếu *một cách âm thầm*, Lean không báo gì cả. Lỗi D59 chính là một trường hợp như vậy. Nói cách khác, vùng tin cậy không chỉ là kernel Lean, mà còn là Aeneas và các mô hình ngoài.

---

## Slide 9 — AI hỗ trợ kiểm chứng như thế nào

*Phần 3 · 10 phút (cùng slide 10–11).*

AI không chỉ sinh mã từ đầu. Bốn vai trò hữu ích hơn nhiều: **giải thích** mã lạ và mục tiêu chứng minh bằng ngôn ngữ tự nhiên; **gợi ý** bổ đề và tactic; **sinh** bản nháp đặc tả, chứng minh — và cả phản ví dụ; **khám phá** các hướng tiếp cận khác khi một chứng minh bị kẹt.

Trong SPQR, AI soạn phần lớn 246 định lý đặc tả, tóm tắt các chuyển trạng thái của giao thức, và đề xuất chính các byte của thông điệp giả mạo trong lỗi D21. Nhưng mỗi thứ AI tạo ra đều phải đi qua Lean hoặc `cargo test`. AI tăng năng suất; nó không thay thế việc kiểm tra.

## Slide 10 — Vì sao chứng minh do AI sinh ra cần được kiểm tra

*Thời lượng: 3 phút.*

Bốn kiểu thất bại, theo thứ tự ngày càng khó phát hiện.

Thất bại 1, *chứng minh không hợp lệ*: mã không biên dịch hoặc không chứng minh được mục tiêu. Dễ nhất — Lean bắt được ngay.

Thất bại 2, *sai tính chất*: chứng minh được một mệnh đề yếu hơn mệnh đề cần thiết. Ví dụ: ta cần chứng minh "nếu thông điệp chưa xác thực thì trạng thái mới bằng trạng thái cũ". Nếu AI chỉ chứng minh "hàm xác thực trả về `false` với thông điệp không hợp lệ", Lean sẽ chấp nhận — nhưng hai mệnh đề này không tương đương. Mệnh đề thứ hai không nói gì về việc trạng thái có bị thay đổi hay không.

Thất bại 3, *thiếu giả thiết*: mô hình bỏ sót một phần hành vi của hệ thống. Thất bại 4, *tự tin sai*: chứng minh thành công bị diễn giải thành "toàn bộ hệ thống an toàn".

Thanh dưới là quy trình: AI đề xuất → Lean kiểm tra chứng minh → con người kiểm tra đặc tả và giả thiết. Hai bước sau không thể bỏ.

## Slide 11 — Fuzzing cho thấy gì — và không cho thấy gì

*Phần 3 · bằng chứng.*

Hình trái: một harness do AI xây dựng gửi 40.000 thông điệp giả mạo vào SPQR. Không có panic. Nếu dừng ở đây, kết luận sẽ là "an toàn". Nhưng lỗi D21 nằm trên đường màu xanh — đường thông điệp *được chấp nhận*. Harness chỉ hỏi "có crash không?", không hỏi "trạng thái có bị thay đổi sai không?".

Hình phải: trong Lean, bộ đếm thông điệp có một giới hạn trên được dùng làm *giả thiết* của nhiều định lý. Một peer có thể vượt giới hạn đó sau khoảng 156 nghìn thông điệp. Định lý vẫn đúng — nhưng chỉ đúng khi giả thiết còn đúng.

Cả hai công cụ đều "pass". Cả hai đều không đặt đúng câu hỏi. Đây là minh họa cụ thể cho thất bại 2 và 3 ở slide trước.

---

## Slide 12 — Dự án: SPQR của Signal, kiểm chứng lại bằng Lean 4

*Phần 4 · 15 phút (slide 12–19).*

Bây giờ vào phần chính. SPQR là lớp ML-KEM — tức lớp hậu lượng tử — trong Triple Ratchet của Signal, crate Rust `spqr` phiên bản 1.5.0. Signal đã kiểm chứng nó bằng hax và F*. Chúng tôi kiểm chứng lại một cách độc lập bằng Rust → Aeneas → Lean 4, 246 định lý, không `sorry`. Kết quả: 63 lỗi, D1 đến D63, mỗi lỗi đi kèm hoặc một chứng minh Lean, hoặc một phản ví dụ Rust chạy được.

Ba nhóm nguyên nhân gốc. Nhóm một, đóng khung đỏ: **xác thực sau khi đã lưu trạng thái** — sáu lỗi, D21 là đại diện. Nhóm hai: `from_pb` sao chép dữ liệu mà không kiểm tra — đây là nhóm của D1. Nhóm ba: các khẳng định `assume!` dùng cho chứng minh nhưng bị xóa khi chạy thật — tức là giả thiết của định lý không được mã thực thi.

Nhận xét: cả ba nhóm đều có cùng một bản chất — *khoảng cách giữa điều chứng minh giả định và điều mã thực sự kiểm tra*.

## Slide 13 — 63 lỗi nhìn tổng quát

*Phần 4 · bằng chứng.*

Biểu đồ trái là trạng thái sửa. Biểu đồ phải phân loại theo nguyên nhân: tràn số và thiếu kiểm tra đầu vào chiếm đa số về số lượng. Nhưng nhóm màu đỏ — sai thứ tự xác thực — tuy ít về số lượng lại nghiêm trọng nhất về hậu quả, và là case study hôm nay.

## Slide 14 — Case study: khi giao thức chấp nhận nhầm thông điệp

*Phần 4 · D21.*

Mục tiêu bảo mật — chính là câu đặc tả ở slide 6: một thông điệp điều khiển chưa xác thực không được gây ra chuyển trạng thái trái phép.

Bên trái, màu xanh, là hành vi đúng: nhận, xác thực, kiểm tra ngữ nghĩa, rồi mới chuyển trạng thái. Bên phải, màu đỏ, là điều hàm `recv` của SPQR thực sự làm: nhận, **tiến epoch và lưu trạng thái**, rồi mới xác thực, và nếu xác thực thất bại thì từ chối thông điệp — nhưng trạng thái đã thay đổi rồi.

Câu hỏi then chốt: điều gì xảy ra khi thông điệp bị từ chối *sau khi* trạng thái đã thay đổi? Hãy dừng vài giây để người nghe tự suy nghĩ trước khi sang slide sau.

## Slide 15 — D21 dưới dạng sơ đồ tuần tự

*Phần 4 · bằng chứng.*

Đây là câu trả lời. Alice và Bob đang ở epoch 1. Một thông điệp giả mạo chỉ 4 byte — không cần khóa, không cần MAC hợp lệ — đến Bob. Bob tiến lên epoch 2 trước khi kiểm tra MAC, rồi từ chối thông điệp. Nhưng Bob đã ở epoch 2.

Từ đó: mọi thông điệp Bob gửi đi mang epoch 2, Alice ở epoch 1 từ chối tất cả. Mọi thông điệp Alice gửi mang epoch 1, Bob ở epoch 2 bỏ qua tất cả. Deadlock vĩnh viễn; phiên không bao giờ tự phục hồi. Đây là một lỗi từ chối dịch vụ không cần phá mật mã.

Phản ví dụ này được tái hiện bằng `cargo test` và được chứng minh trong `Spqr/Specs/Bugs/ProtocolDoS.lean`.

## Slide 16 — MAC được kiểm tra ở đâu — và không được kiểm tra ở đâu

*Phần 4 · bằng chứng.*

Máy trạng thái của `recv`. Cạnh xanh là những cạnh *duy nhất* gọi MAC. Cạnh đỏ là những cạnh lưu trạng thái mà không gọi Authenticator nào. D21 là cạnh quay lui màu đỏ.

Giá trị của hình này: nó cho thấy D21 không phải lỗi cá biệt mà là một *mẫu* — cùng cấu trúc giải thích D16, D22, D35, D36 và D62. Khi tìm được một lỗi, câu hỏi tiếp theo luôn là "còn chỗ nào có cùng hình dạng?".

## Slide 17 — Vì sao Signal an toàn trước D21 — và ai thì không

*Phần 4 · khả năng khai thác.*

Đây là slide về sự trung thực khoa học. Ứng dụng Signal thật *không* bị deadlock. Lý do: libsignal, lớp bao ngoài, gọi `spqr::recv` trên một **bản sao** của trạng thái, và chỉ ghi bản sao đó xuống khi MAC đã qua. Nói cách khác, lớp bảo vệ tồn tại — nhưng nằm *bên ngoài* crate SPQR.

Hệ quả: bất kỳ ai dùng crate SPQR trực tiếp mà không có lớp bao đó — một embedder khác, một cài đặt peer, hay chính kho lưu trữ nếu blob bị ghi đè — đều bị ảnh hưởng.

Bài học: *khả năng khai thác* là một phán xét về toàn bộ hệ thống, không phải về một crate. Phán xét này không đến từ Lean, cũng không từ AI, mà từ việc đọc mã libsignal. Đây là lý do con người vẫn cần ở trong vòng lặp.

## Slide 18 — Từ đọc mã đến lỗi được xác nhận

*Phần 4 · quy trình.*

Bốn bước, với D21 làm ví dụ cụ thể viết bằng màu đỏ dưới mỗi bước.

Bước 1, *quan sát*: AI đọc `recv` và tóm tắt luồng điều khiển; nó chỉ ra rằng epoch tiến lên trước khi kiểm tra MAC. Bước 2, *giả thuyết*: một thông điệp chưa xác thực có thể đưa peer sang epoch mới. Bước 3, *xây dựng*: AI đề xuất chuỗi 4 byte giả mạo. Bước 4, *xác nhận*: `cargo test` tái hiện deadlock; Lean chứng minh tính chất trong `ProtocolDoS.lean`.

Trong thực tế chúng tôi dùng hai agent với vai trò bổ sung: một agent cố gắng chứng minh tính chất mong muốn, một agent phản biện — tìm giả thiết thiếu, trường hợp biên, phản ví dụ. Nhưng thanh dưới là điều quan trọng nhất: **hai agent đồng ý với nhau không phải là bằng chứng.** Cả hai có thể cùng sai. Chỉ báo cáo lỗi khi có bằng chứng độc lập, chạy được hoặc kiểm tra được bằng máy.

## Slide 19 — Ba vai trò bổ sung, một lỗi

*Phần 4 · phương pháp.*

Tóm tắt phần 4 bằng một hình. AI đề xuất — giả thuyết, chiến lược chứng minh, kịch bản thất bại. Công cụ hình thức kiểm tra — tính hợp lệ của chứng minh, các tính chất đã phát biểu, phản ví dụ trong mô hình. Con người đánh giá — chất lượng đặc tả, khả năng khai thác thực tế, tác động bảo mật.

Với D21: byte giả mạo đến từ AI; chứng minh deadlock từ cargo và Lean; kết luận về khả năng khai thác từ việc đọc libsignal. Không mũi tên nào bỏ qua được. Không nên trình bày AI như công cụ tự động tìm mọi lỗ hổng; vai trò của nó là mở rộng không gian khám phá, không loại bỏ nhu cầu kiểm chứng.

---

## Slide 20 — Vì sao một chứng minh không phải là bảo đảm an toàn

*Phần 5 · 7 phút (slide 20–22).*

Hình này là toàn bộ bài nói trong một bức tranh. Ellipse xanh dương là những gì được máy kiểm tra: các định lý, dưới các giả thiết của chúng, trong mô hình. Vùng xanh lá là hệ thống thật: mã Rust, lưu trữ, peer, lớp bao libsignal, môi trường chạy.

Mọi lỗi trong 63 lỗi đều là một *mệnh đề đúng về vùng xanh lá mà không định lý nào nhắc đến*. Chứng minh không sai. Chúng chỉ không nói về điều đó.

## Slide 21 — Thông điệp chính

*Phần 5.*

Đọc chậm, từng câu.

Ngay cả một chứng minh Lean được kernel chấp nhận cũng chỉ thiết lập mệnh đề hình thức dưới các giả thiết đã nêu.

Nó không tự thân thiết lập rằng đặc tả đã nắm bắt được mọi yêu cầu bảo mật của hệ thống thật.

SPQR: 246 file đặc tả, không `sorry`, bất biến chuỗi `ChainInv` được chứng minh — và vẫn có 63 lỗi, được tìm ra *chính xác bằng cách hỏi mỗi chứng minh phải giả định điều gì*. Hỏi về giả thiết không phải là điểm yếu của phương pháp; đó chính là phương pháp.

## Slide 22 — Bài học, giới hạn và điểm rút ra

*Phần 5.*

Năm điểm. Một: testing hữu ích nhưng không đầy đủ — 40.000 thông điệp fuzz bỏ sót D21. Hai: kiểm chứng hình thức cho bảo đảm chính xác, nhưng tương đối với đặc tả và giả thiết. Ba: AI tăng tốc khám phá — soạn đặc tả, chứng minh, harness, phản ví dụ. Bốn: chứng minh không đồng nghĩa với an toàn. Năm: phán xét của con người vẫn thiết yếu — kết luận về libsignal đến từ đọc mã, không từ trợ lý chứng minh.

Ba câu hỏi thảo luận bên phải. Tôi muốn kết bằng câu thứ hai: **một chương trình được kiểm chứng hoàn hảo vẫn có thể không an toàn không?** Câu trả lời là có — nếu đặc tả không mô tả đúng yêu cầu bảo mật, nếu mô hình bỏ sót một phần hệ thống, hoặc nếu giả thiết không đúng trong môi trường thật. Đó là điểm kết nối ba chủ đề AI, Lean và bảo mật.

Thông điệp cuối: dùng AI để khám phá nhiều khả năng hơn — và dùng kiểm chứng để kiểm tra các khẳng định.

## Slide 23 — Cảm ơn

*Thời lượng: còn lại cho hỏi đáp.*

Cảm ơn mọi người. Toàn bộ tài liệu — báo cáo, danh sách 63 lỗi, phân loại, phân tích khả năng khai thác từ xa, các file Lean chứng minh lỗi và phản ví dụ Rust — đều có trong kho mã theo các đường dẫn trên slide. Rất mong nhận được câu hỏi và trao đổi.

---

## Phân bổ thời gian

| Phần | Slide | Thời lượng |
|---|---|---|
| Mở đầu & lộ trình | 1–2 | 2 phút |
| 1 · Có tin phần mềm được không | 3–4 | 5 phút |
| 2 · Kiểm chứng hình thức & Lean | 5–8 | 8 phút |
| 3 · AI hỗ trợ kiểm chứng | 9–11 | 10 phút |
| 4 · Case study SPQR | 12–19 | 15 phút |
| 5 · Bài học & thảo luận | 20–23 | 5 phút |
| **Tổng** | | **45 phút** |

Nếu cần dành 5–7 phút hỏi đáp riêng: rút phần 4 xuống khoảng 12 phút bằng cách lướt nhanh slide 13 (biểu đồ 63 lỗi) và gộp slide 16–17 thành một ý ("mẫu lỗi lặp lại; Signal được bảo vệ bởi lớp ngoài").
