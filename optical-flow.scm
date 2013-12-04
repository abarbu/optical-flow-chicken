(module optical-flow *
(import chicken scheme foreign traversal linear-algebra
        image-processing define-structure scheme2c-compatibility imlib2 foreigners
        srfi-1 posix extras matlab libzip ffmpeg-video lolevel
        random-bsd)

(foreign-declare #<<EOF

double *average_optical_flow_ssv_from_c(double *ssv,
					unsigned height,
					unsigned width,
					unsigned xl,
					unsigned xh,
					unsigned yl,
					unsigned yh) {
  double ax = 0.0, ay = 0.0;
  for (int y = yl; y<=yh; y++) {
    for (int x = xl; x<=xh; x++) {
      ax += ssv[x+y*width];
      ay += ssv[width*height+x+y*width];
    }
  }

  double *average_flow = (double *)malloc(sizeof(double)*2);
  if (average_flow == NULL) {
    fprintf(stderr, "out of memory in average_optical_flow_ssv_from_c\n");
    exit(EXIT_FAILURE);
  }

  average_flow[0] = ax/(((xh-xl)+1)*((yh-yl)+1));
  average_flow[1] = ay/(((xh-xl)+1)*((yh-yl)+1));
  return average_flow;
}

                                        
double integral_optical_flow_area(double *integral_flow,
				  const unsigned height,
				  const unsigned width,
				  unsigned x1, unsigned y1,
				  unsigned x2, unsigned y2) {
  x1 = (x1+1 >= width ? width-2 : x1);
  y1 = (y1+1 >= height ? height-2 : y1);
  x2 = (x2+1 >= width ? width-2 : x2);
  y2 = (y2+1 >= height ? height-2 : y2);
  return integral_flow[x1+y1*width]
    - integral_flow[(x2+1)+y1*width]
    - integral_flow[x1+(y2+1)*width]
    + integral_flow[(x2+1)+(y2+1)*width];
}

void integral_optical_flow_f(double *flow, double *integral,
			     const unsigned height,
			     const unsigned width) {
  for(int y = height - 1; y >= 0; --y)
    for(int x = width - 1; x >= 0; --x)
      integral[x+y*width] =
	flow[x+y*width]
	+ (y+1 >= height ? 0 : integral[x+(y+1)*width])
	+ (x+1 >= width  ? 0 : integral[(x+1)+y*width])
	- (x+1 >= width || y+1 >= height ? 0 : integral[(x+1)+(y+1)*width]);
}

double *integral_optical_flow(double *flow,
			      const unsigned height,
			      const unsigned width) {
  double *integral = malloc(sizeof(double)*height*width*2);
  integral_optical_flow_f(flow, integral, height, width);
  integral_optical_flow_f(flow+height*width, integral+height*width, height, width);
  return integral;
}

void write_flo_to_stream(double *matrix,
			 const unsigned width, const unsigned height,
			 FILE *stream) {
  float *float_matrix = malloc(width*height*2*sizeof(float));
  for(unsigned i = 0; i < width*height; ++i)
    float_matrix[i*2] = matrix[i];
  for(unsigned i = 0; i < width*height; ++i)
    float_matrix[i*2+1] = matrix[width*height+i];

  fprintf(stream, "PIEH");
  if (fwrite(&width, sizeof(int), 1, stream) != 1 ||
      fwrite(&height, sizeof(int), 1, stream) != 1) {
    fprintf(stderr,"flo file: couldn't write width and height\n");
    abort();
  }
  if (fwrite(float_matrix, sizeof(float), 2*width*height, stream) != 2*width*height) {
    fprintf(stderr,"flo file: problem writing data");
    abort();
  }
  free(float_matrix);
  return;
}

double *read_flo_from_stream(FILE *file) {
  /* TODO flo files can have unknown values in them, this is unimplemented */
  const float TAG = 202021.25;
  float tag;
  uint32_t width, height;
  fread(&tag, sizeof(float), 1, file);
  fread(&width, sizeof(uint32_t), 1, file);
  fread(&height, sizeof(uint32_t), 1, file);
  if(tag != TAG) {
    fprintf(stderr,"flo file: bad tag %f (%dx%d)\n", tag, width, height);
    abort();
  }
  const int size = width*height*2;
  float *float_matrix = malloc(size*sizeof(float));
  int ret = 0;
  if( (ret = fread(float_matrix, sizeof(float), size, file)) != size ) {
    fprintf(stderr,"flo file: too short %d != %d\n", ret, size);
    abort();
  }
  double *matrix = malloc(size*sizeof(double));
  for(unsigned i = 0; i < size; i += 2)
    matrix[i/2] = float_matrix[i];
  for(unsigned i = 1; i < size; i += 2)
    matrix[i/2+width*height] = float_matrix[i];
  free(float_matrix);
  return matrix;
}

int32_t* read_flo_size_from_stream(FILE *file) {
  const float TAG = 202021.25;
  float tag;
  fread(&tag, sizeof(float), 1, file);
  if(tag != TAG) {
    printf("flo file: bad tag %f\n", tag);
    abort();
  }
  int32_t *size = malloc(2 * sizeof(int32_t));
  int ret = 0;
  if( (ret = fread(size, sizeof(int32_t), 2, file)) != 2 ) {
    printf("flo file: too short %d != %d\n", ret, 2);
    abort();
  }
  return size;
}

EOF
)

;; Belong elsewhere

(define (safe-matrix-ref m y x default)
 (if (or (>= x (matrix-columns m)) (< x 0)
	(>= y (matrix-rows m)) (< y 0))
     default
     (matrix-ref m y x)))

(define (random-partition l)
 (let* ((pivot (random-integer (length l)))
	(pivot-element (list-ref l pivot))
	(l (list-remove l pivot))
	(first-half (remove-if-not (lambda (e) (< e pivot-element)) l))
	(second-half (remove-if (lambda (e) (< e pivot-element)) l)))
  (list (list (+ (length first-half) 1) pivot-element)
	first-half
	second-half)))

(define (k-smallest-in-linear-time l k)
 (cond
  ((null? l) (panic "k-smallest: k is out of boundary."))
  ((and (= (length l) 1) (= k 1)) (first l))
  (else
   (let* ((partition-result (random-partition l))
	  (pivot (first (first partition-result)))
	  (pivot-element (second (first partition-result)))
	  (first-half (second partition-result))
	  (second-half (third partition-result)))
    (cond
     ((= pivot k) pivot-element)
     ((< pivot k) (k-smallest-in-linear-time second-half (- k pivot)))
     (else (k-smallest-in-linear-time first-half k)))))))

(define (clip v low high) (max (min v high) low))

;;; Optical flow
;;; http://perception.inrialpes.fr/~chari/myweb/Software/
;;; High accuracy optical flow estimation based on a theory for warping
;;; Thomas Brox, Andrés Bruhn, Nils Papenberg, Joachim Weickert
;;; European Conference on Computer Vision (ECCV), Prague, Czech Republic, May 2004.

;; boxes are vectors '#(x1 y1 x2 y2)

(define-structure c-optical-flow handle width height)

(define (read-flo-from-file-to-scheme filename)
 (with-file-stream read-flo-from-stream-to-scheme filename "r"))

(define (read-flo-from-buffer-to-scheme buffer size)
 (with-buffer-stream read-flo-from-stream-to-scheme buffer size "r"))

(define (read-flo-from-stream-to-scheme file)
 (let* ((size-ptr
	 ((c-function c-pointer ("read_flo_size_from_stream" c-pointer)) file))
	(size (vector (c-int-ref size-ptr 0) (c-int-ref size-ptr 4)))
	(matrix-ptr
	 ((c-function c-pointer ("read_flo_from_stream" c-pointer)) file)))
  (let ((xs (map-n-vector
              (lambda (ho)
               (map-n-vector
                 (lambda (wo) (c-float-ref matrix-ptr
                                      (* (+ (* (+ (* ho (x size)) wo) 2) 0) 4)))
                (x size)))
	     (y size)))
	(ys (map-n-vector
              (lambda (ho)
               (map-n-vector
                 (lambda (wo) (c-float-ref matrix-ptr
                                      (* (+ (* (+ (* ho (x size)) wo) 2) 1) 4)))
                (x size)))
	     (y size))))
   (free matrix-ptr)
   (free size-ptr)
   (list xs ys))))

(define (read-flo-from-file filename)
 (let ((size (with-file-stream read-flo-size-from-stream filename "r")))
  (with-file-stream (lambda (file) (read-flo-from-stream file size)) filename "r")))

(define (read-flo-from-buffer buffer buffer-size)
 (let ((size (with-buffer-stream read-flo-size-from-stream
				 buffer buffer-size "r")))
  (with-buffer-stream (lambda (file) (read-flo-from-stream file size))
		      buffer buffer-size "r")))

(define (read-flo-size-from-stream file)
 (let* ((size-ptr
	 ((c-function c-pointer ("read_flo_size_from_stream" c-pointer)) file))
	(size (vector (c-int-ref size-ptr 0) (c-int-ref size-ptr 4))))
  (free size-ptr)
  size))

(define (read-flo-from-stream file size)
 (make-c-optical-flow ((c-function c-pointer ("read_flo_from_stream" c-pointer)) file)
		      (x size) (y size)))

(define (write-flo-to-file flow filename)
 (with-file-stream (lambda (file) (write-flo-to-stream flow file))
		   filename "w"))

(define (write-flo-to-buffer flow buffer size)
 (with-buffer-stream (lambda (file) (write-flo-to-stream flow file)) buffer size "w"))

(define (write-flo-to-stream flow file)
 ((c-function void ("write_flo_to_stream" c-pointer unsigned-integer unsigned-integer c-pointer))
  (c-optical-flow-handle flow) (c-optical-flow-width flow)
  (c-optical-flow-height flow) file))

(define (integral-optical-flow-from-c optical-flow width height)
 ((c-function c-pointer ("integral_optical_flow" c-pointer unsigned-integer unsigned-integer))
  optical-flow height width))

(define c-integral-optical-flow-area
 (c-function double ("integral_optical_flow_area"
		     c-pointer unsigned-integer unsigned-integer
		     unsigned-integer unsigned-integer unsigned-integer unsigned-integer)))

;; Note that this internally clips to the border of the image
(define (average-integral-optical-flow-in-c
    optical-flow x1 y1 x2 y2)
 (k*v 2 (vector
	 (/ ((c-function double ("integral_optical_flow_area"
				 c-pointer unsigned-integer unsigned-integer
				 unsigned-integer unsigned-integer unsigned-integer unsigned-integer))
	     (c-optical-flow-handle optical-flow)
	     (c-optical-flow-height optical-flow)
	     (c-optical-flow-width  optical-flow)
	     x1 y1 x2 y2)
	    (* (+ (- x2 x1) 1) (+ (- y2 y1) 1)))
	 (/ ((c-function double ("integral_optical_flow_area"
				 c-pointer unsigned-integer unsigned-integer
				 unsigned-integer unsigned-integer unsigned-integer unsigned-integer))
	     (pointer+
              (c-optical-flow-handle optical-flow)
              (* (c-optical-flow-height optical-flow)
                 (c-optical-flow-width  optical-flow)
                 c-sizeof-double))
	     (c-optical-flow-height optical-flow)
	     (c-optical-flow-width  optical-flow)
	     x1 y1 x2 y2)
	    (* (+ (- x2 x1) 1) (+ (- y2 y1) 1))))))

(define (get-optical-flow-at-pixel optical-flow x y)
 (k*v 2 (vector
	 ((c-function double ("integral_optical_flow_area"
			      c-pointer unsigned-integer unsigned-integer
			      unsigned-integer unsigned-integer unsigned-integer unsigned-integer))
	  (c-optical-flow-handle optical-flow)
	  (c-optical-flow-height optical-flow)
	  (c-optical-flow-width  optical-flow)
	  x y x y)
	 ((c-function double ("integral_optical_flow_area"
                              c-pointer unsigned-integer unsigned-integer
                              unsigned-integer unsigned-integer unsigned-integer unsigned-integer))
	  (pointer+
           (c-optical-flow-handle optical-flow)
           (* (c-optical-flow-height optical-flow)
              (c-optical-flow-width  optical-flow)
              c-sizeof-double))
	  (c-optical-flow-height optical-flow)
	  (c-optical-flow-width  optical-flow)
	  x y x y))))

(define (average-optical-flow-non-integral-c
    ssv height width x1 y1 x2 y2)
 (let ((v ((c-function c-pointer ("average_optical_flow_ssv_from_c"
                                  c-pointer unsigned-integer unsigned-integer
                                  unsigned-integer unsigned-integer unsigned-integer unsigned-integer))
	   ssv height width x1 x2 y1 y2)))
  (vector (c-double-ref v 0) (c-double-ref v c-sizeof-double))))

(define (average-flow-in-box box flow-transformation)
 (k*v 2 (average-integral-optical-flow-in-c
	 flow-transformation
	 (clip (exact-round (/ (vector-ref box 0) 2)) 0
               (- (c-optical-flow-width flow-transformation) 1))
	 (clip (exact-round (/ (vector-ref box 1) 2)) 0
               (- (c-optical-flow-height flow-transformation) 1))
	 (clip (exact-round (/ (vector-ref box 2) 2)) 0
               (- (c-optical-flow-width flow-transformation) 1))
	 (clip (exact-round (/ (vector-ref box 3) 2)) 0
               (- (c-optical-flow-height flow-transformation) 1)))))

(define (median-flow-in-box box flow-transformation)
 (let* ((x1 (clip (exact-round (/ (vector-ref box 0) 2)) 0
                  (- (c-optical-flow-width flow-transformation) 1)))
	(y1 (clip (exact-round (/ (vector-ref box 1) 2)) 0
                  (- (c-optical-flow-height flow-transformation) 1)))
	(x2 (clip (exact-round (/ (vector-ref box 2) 2)) 0
                  (- (c-optical-flow-width flow-transformation) 1)))
	(y2 (clip (exact-round (/ (vector-ref box 3) 2)) 0
                  (- (c-optical-flow-height flow-transformation) 1)))
	(flow-magnitudes
	 (reduce append
		 (map-n
                   (lambda (y)
                    (map-n
                      (lambda (x)
                       (magnitude (get-optical-flow-at-pixel flow-transformation
                                                             (+ x x1) (+ y y1))))
                     (+ (- x2 x1) 1)))
		  (+ (- y2 y1) 1))
		 '()))
	(len (length flow-magnitudes)))
  (k-smallest-in-linear-time flow-magnitudes (exact-floor (* len (/ 2 3))))))

(define (integral-matrix-rectangle i x1 y1 x2 y2)
 (+ (matrix-ref i y1 x1)
    (- (safe-matrix-ref i y1 (+ x2 1) 0))
    (- (safe-matrix-ref i (+ y2 1) x1 0))
    (safe-matrix-ref i (+ y2 1) (+ x2 1) 0)))

(define (optical-flow image-prev-filename image-next-filename)
 (matlab "addpath('~/darpa-collaboration/optical-flow/sand/')")
 (matlab (format #f "[u, v] = optic_flow_sand(imread('~a'),imread('~a'));"
		 image-prev-filename
		 image-next-filename))
 (list (matlab-get-variable "u")
       (matlab-get-variable "v")))

(define (average-optical-flow transformation x-low x-high y-low y-high)
 ;; The Matlab code has no scaling but we believe it should be scaled by 2.0
 ;; since the optical flow is downsampled by a factor of 2.0.
 (k*v 2.0
      (map-vector /
		  (integral-matrix-rectangle transformation
					     x-low x-high y-low y-high)
		  (vector (- x-high x-low) (- y-high y-low)))))

(define (show-quiver u v)
 (scheme->matlab! "u" u)
 (scheme->matlab! "v" v)
 (matlab "quiver(u,v,0)"))
)

