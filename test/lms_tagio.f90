! test/lms_tagio.f90: PRINT for test/two_path.bb. Each value is one line, tagged with its
! type and kind -- I<k>:<integer>, B<k>:<the real's bits as an integer>, C<k>:<re bits>,<im bits>,
! L:T, S:<text> -- and a record ends with "/". test/two_path_run.clj prints the same for clotran,
! so the two paths are compared value by value, each real bit for bit in its kind.
module lms_tagio
  use, intrinsic :: iso_fortran_env, only: int8, int16, int32, int64, real32, real64
  implicit none
  private
  public :: lms_tag, lms_tag_end
  interface lms_tag
    module procedure t_i1, t_i2, t_i4, t_i8, t_r4, t_r8, t_c4, t_c8, t_l, t_s, &
      a_i1, a_i2, a_i4, a_i8, a_r4, a_r8, a_c4, a_c8, a_l, a_s
  end interface lms_tag
contains
  subroutine t_i1(x)
    integer(int8), intent(in) :: x
    write(*,'(a,i0)') 'I1:', x
  end subroutine t_i1
  subroutine a_i1(x)
    integer(int8), intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_i1(x(i))
    end do
  end subroutine a_i1
  subroutine t_i2(x)
    integer(int16), intent(in) :: x
    write(*,'(a,i0)') 'I2:', x
  end subroutine t_i2
  subroutine a_i2(x)
    integer(int16), intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_i2(x(i))
    end do
  end subroutine a_i2
  subroutine t_i4(x)
    integer(int32), intent(in) :: x
    write(*,'(a,i0)') 'I4:', x
  end subroutine t_i4
  subroutine a_i4(x)
    integer(int32), intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_i4(x(i))
    end do
  end subroutine a_i4
  subroutine t_i8(x)
    integer(int64), intent(in) :: x
    write(*,'(a,i0)') 'I8:', x
  end subroutine t_i8
  subroutine a_i8(x)
    integer(int64), intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_i8(x(i))
    end do
  end subroutine a_i8
  subroutine t_r4(x)
    real(real32), intent(in) :: x
    write(*,'(a,i0)') 'B4:', transfer(x, 0_int32)
  end subroutine t_r4
  subroutine a_r4(x)
    real(real32), intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_r4(x(i))
    end do
  end subroutine a_r4
  subroutine t_r8(x)
    real(real64), intent(in) :: x
    write(*,'(a,i0)') 'B8:', transfer(x, 0_int64)
  end subroutine t_r8
  subroutine a_r8(x)
    real(real64), intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_r8(x(i))
    end do
  end subroutine a_r8
  subroutine t_c4(x)
    complex(real32), intent(in) :: x
    write(*,'(a,i0,a,i0)') 'C4:', transfer(real(x), 0_int32), ',', transfer(aimag(x), 0_int32)
  end subroutine t_c4
  subroutine a_c4(x)
    complex(real32), intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_c4(x(i))
    end do
  end subroutine a_c4
  subroutine t_c8(x)
    complex(real64), intent(in) :: x
    write(*,'(a,i0,a,i0)') 'C8:', transfer(real(x), 0_int64), ',', transfer(aimag(x), 0_int64)
  end subroutine t_c8
  subroutine a_c8(x)
    complex(real64), intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_c8(x(i))
    end do
  end subroutine a_c8
  subroutine t_l(x)
    logical, intent(in) :: x
    if (x) then
      write(*,'(a)') 'L:T'
    else
      write(*,'(a)') 'L:F'
    end if
  end subroutine t_l
  subroutine a_l(x)
    logical, intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_l(x(i))
    end do
  end subroutine a_l
  subroutine t_s(x)
    character(len=*), intent(in) :: x
    write(*,'(a)') 'S:' // x
  end subroutine t_s
  subroutine a_s(x)
    character(len=*), intent(in) :: x(:)
    integer :: i
    do i = 1, size(x)
      call t_s(x(i))
    end do
  end subroutine a_s
  subroutine lms_tag_end()
    write(*,'(a)') '/'
  end subroutine lms_tag_end
end module lms_tagio
